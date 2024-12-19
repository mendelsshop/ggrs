use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct EncodedInputSequence {
    /// Size of each input in the sequence relative to the reference input for the first input, and
    /// relative input N-1 for input N for all inputs after the first.
    ///
    /// If None, then all inputs are the same size as the reference input (and hence the length of
    /// [Self::input_bytes] must be a multiple of the length of the reference input).
    input_sizes: Option<Vec<i32>>,
    encoded_bytes: Vec<u8>,
}

pub(crate) fn encode<'a>(reference: &[u8], pending_input: Vec<&[u8]>) -> Vec<u8> {
    // first, do a XOR encoding to the reference input (will probably lead to a lot of same bits in
    // sequence)
    let mut encoded = delta_encode(reference, pending_input);

    // then, RLE encode the buffer (making use of the property mentioned above)
    encoded.encoded_bytes = bitfield_rle::encode(encoded.encoded_bytes);

    // then serialize the encoded input sequence
    bincode::serialize(&encoded).expect("input serialization failed")
}

fn delta_encode<'a>(ref_bytes: &[u8], pending_input: Vec<&[u8]>) -> EncodedInputSequence {
    let input_sizes = if pending_input
        .iter()
        .all(|input| input.len() == ref_bytes.len())
        && ref_bytes.len() > 0
    {
        // In the common case where all inputs are the same size as a non-zero-sized reference
        // input, we can leave the input sizes out to allow the receiver to infer the size from the
        // reference and save a bit of space.
        None
    } else {
        // We encode the inputs relative to the reference input for the first input, and relative
        // input N-1 for input N for all inputs after the first; assuming that inputs are likely to
        // be close in size to each previous input, this should bring each individual input size to
        // be stored closer to 0, which will in turn allow these to be serialized using fewer bytes
        // when a varint encoding scheme is used by the serde serializer.
        let mut input_sizes = Vec::with_capacity(pending_input.len());
        let mut base_size = ref_bytes.len();
        for input_size in pending_input.iter().map(|input| input.len()) {
            assert!(
                input_size <= i32::MAX as usize,
                "each pending input must be less than 2^31 bytes in size"
            );
            input_sizes.push(input_size as i32 - base_size as i32);
            base_size = input_size;
        }
        Some(input_sizes)
    };

    let encoded_bytes = {
        let mut encoded_bytes = Vec::with_capacity(pending_input.iter().map(|inp| inp.len()).sum());

        // We encode the first pending input relative to the reference input, and then encode each
        // subsequent pending input N relative to (the encoded) pending input N-1.
        let mut base = ref_bytes;
        for input in pending_input.iter() {
            for (base_byte, input_byte) in base.iter().zip(input.iter()) {
                encoded_bytes.push(base_byte ^ input_byte);
            }

            // Append remaining bytes from the input if it's longer than the base
            if input.len() > base.len() {
                encoded_bytes.extend_from_slice(&input[base.len()..]);
            }

            // use the current input as the base for the next input to be encoded against
            base = input;
        }
        encoded_bytes
    };

    EncodedInputSequence {
        input_sizes,
        encoded_bytes,
    }
}

pub(crate) fn decode(
    reference: &[u8],
    data: &[u8],
) -> Result<Vec<Vec<u8>>, Box<dyn std::error::Error + Send + Sync>> {
    // deserialize the encoded input sequence
    let mut encoded: EncodedInputSequence = bincode::deserialize(data)?;

    // decode the RLE encoding first
    encoded.encoded_bytes = bitfield_rle::decode(encoded.encoded_bytes)?;

    // decode the delta-encoding
    delta_decode(reference, &encoded)
}

fn delta_decode(
    ref_bytes: &[u8],
    encoded: &EncodedInputSequence,
) -> Result<Vec<Vec<u8>>, Box<dyn std::error::Error + Send + Sync>> {
    // decode expected input sizes, which will tell us how to break up the bytes (and also how many
    // inputs there will be)
    let input_sizes = if let Some(input_sizes_rel) = &encoded.input_sizes {
        let mut input_sizes = Vec::with_capacity(input_sizes_rel.len());

        // probably we'd run out of memory anyway when dealing with a reference input this large,
        // but it doesn't hurt to check - better to bail out with an error than panic on bad inputs.
        let mut base_size = if ref_bytes.len() > i32::MAX as usize {
            return Err(Box::new(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("Reference input is too large: {} bytes", ref_bytes.len()),
            )));
        } else {
            ref_bytes.len() as i32
        };

        for input_size_rel in input_sizes_rel {
            let input_size = base_size as i32 + input_size_rel;
            if input_size < 0 {
                return Err(Box::new(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("Input size is negative: {input_size}"),
                )));
            }
            input_sizes.push(input_size as usize);
            base_size = input_size;
        }
        input_sizes
    } else {
        if ref_bytes.len() == 0 {
            return Err(Box::new(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Reference bytes must be > 0 bytes to decode \
                a sequence of inputs of unknown size",
            )));
        }
        let input_count = encoded.encoded_bytes.len() / ref_bytes.len();
        vec![ref_bytes.len(); input_count]
    };

    // make sure input sizes is consistent with how many bytes we have to decode
    let total_bytes_expected = input_sizes.iter().sum::<usize>();
    if total_bytes_expected != encoded.encoded_bytes.len() {
        return Err(Box::new(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!(
                "Received input bytes length ({}) that did not \
                match expected input sizes ({:?}, sum={})",
                encoded.encoded_bytes.len(),
                input_sizes,
                total_bytes_expected
            ),
        )));
    }

    // use the input sizes to actually decode the inputs
    let mut decoded_inputs = Vec::with_capacity(input_sizes.len());
    let mut pos = 0;
    let mut base_input_bytes = ref_bytes;
    for input_size in input_sizes {
        let input_bytes = &encoded.encoded_bytes[pos..pos + input_size];

        let mut buffer = input_bytes.to_vec();

        // decode those bytes that overlap with our reference
        for (buffer_byte, (input_byte, base_byte)) in buffer
            .iter_mut()
            .zip(input_bytes.iter().zip(base_input_bytes))
        {
            *buffer_byte = *input_byte ^ *base_byte;
        }

        // if the input size is larger than the base, we expect the remaining bytes to be unencoded
        // and we've already copied from base_input_bytes to buffer, so there's nothing to do
        decoded_inputs.push(buffer);

        pos += input_size;
        base_input_bytes = decoded_inputs.last().unwrap();
    }

    Ok(decoded_inputs)
}

// #########
// # TESTS #
// #########

#[cfg(test)]
mod compression_tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn encode_decode_round_trip(
            reference in prop::collection::vec(any::<u8>(), 0..32),
            inputs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..32), 0..32)
        ) {
            let encoded = encode(&reference, inputs.iter().map(|x| x.as_slice()).collect());
            let decoded = decode(&reference, &encoded).unwrap();

            assert_eq!(inputs, decoded, "original input (left) should match decoded (right)");
        }

        #[test]
        fn decode_arbitrary_input_never_panics(
            reference in prop::collection::vec(any::<u8>(), 0..2048),
            bytes in prop::collection::vec(any::<u8>(), 0..2048)
        ) {
            // it's important that we never panic when decoding arbitrary input since input bytes
            // can be received from attackers - we should just return an error instead
            let _ = decode(&reference, &bytes);
        }
    }

    #[test]
    fn test_encode_decode() {
        let ref_input = vec![0, 0, 0, 1];
        let inp0: Vec<u8> = vec![0, 0, 1, 0];
        let inp1: Vec<u8> = vec![0, 0, 1, 1];
        let inp2: Vec<u8> = vec![0, 1, 0, 0];
        let inp3: Vec<u8> = vec![0, 1, 0, 1];
        let inp4: Vec<u8> = vec![0, 1, 1, 0];

        let pend_inp = vec![inp0, inp1, inp2, inp3, inp4];

        let encoded = encode(&ref_input, pend_inp.iter().map(|x| x.as_slice()).collect());
        let decoded = decode(&ref_input, &encoded).unwrap();

        assert!(pend_inp == decoded);
    }
}
