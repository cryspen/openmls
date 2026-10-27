use ds_lib::{self, *};
use openmls::prelude::*;
use openmls_basic_credential::SignatureKeyPair;
use openmls_rust_crypto::OpenMlsRustCrypto;
use openmls_traits::OpenMlsProvider;
use tls_codec::{Deserialize, Serialize, Size};

#[test]
fn test_client_info() {
    let crypto = &OpenMlsRustCrypto::default();
    let client_name = "Client1";
    let ciphersuite = Ciphersuite::MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519;

    let credential = BasicCredential::new(client_name.as_bytes().to_vec());
    let signature_keys = SignatureKeyPair::new(ciphersuite.signature_algorithm()).unwrap();
    let credential_with_key = CredentialWithKey {
        credential: credential.into(),
        signature_key: signature_keys.to_public_vec().into(),
    };
    signature_keys.store(crypto.storage()).unwrap();

    let client_key_package = KeyPackage::builder()
        .build(ciphersuite, crypto, &signature_keys, credential_with_key)
        .unwrap();

    let client_key_package = vec![(
        client_key_package
            .key_package()
            .hash_ref(crypto.crypto())
            .expect("Could not hash KeyPackage.")
            .as_slice()
            .to_vec(),
        KeyPackageIn::from(client_key_package.key_package().clone()),
    )];
    let client_data = ClientInfo::new(client_key_package);

    let encoded_client_data = client_data.tls_serialize_detached().unwrap();
    let client_data2 = ClientInfo::tls_deserialize(&mut encoded_client_data.as_slice())
        .unwrap()
        .tls_serialize_detached()
        .unwrap();
    assert_eq!(client_data.tls_serialize_detached().unwrap(), client_data2);
}

/// Regression test: the size of `reserved_key_pkg_hash` must be the length of
/// its encoding (it used to count elements, not bytes).
#[test]
fn test_client_info_reserved_hashes_size() {
    let mut client_info = ClientInfo::default();
    client_info.reserved_key_pkg_hash.insert(vec![0xab; 32]);
    client_info.reserved_key_pkg_hash.insert(vec![0xcd; 32]);

    let encoded = client_info.tls_serialize_detached().unwrap();
    assert_eq!(client_info.tls_serialized_len(), encoded.len());

    // In a vector, the derived length prefix relies on the element sizes.
    let client_infos = vec![client_info, ClientInfo::default()];
    let encoded = client_infos.tls_serialize_detached().unwrap();
    assert_eq!(client_infos.tls_serialized_len(), encoded.len());
    let decoded = Vec::<ClientInfo>::tls_deserialize_exact(&encoded).unwrap();
    assert_eq!(decoded.len(), 2);
    assert_eq!(
        decoded[0].reserved_key_pkg_hash,
        client_infos[0].reserved_key_pkg_hash
    );
    assert_eq!(
        decoded.tls_serialize_detached().unwrap().len(),
        encoded.len()
    );
}
