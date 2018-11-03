#SHA256
echo "BENCHMARK: Verifying SHA256 algorithm"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/asm --p2lang asm --verif_mode hybrid --no_alias_analysis

#SHA256 with SSSE3
echo "BENCHMARK: Verifying SHA256 algorithm with SSSE3 extension"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/asm --p2lang asm --verif_mode hybrid --no_alias_analysis

#sha_naive_to_ssse
echo "BENCHMARK: Verifying equivalence between SHA256 algorithm and SHA256 with SSSE3 extension"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/sha_naive_to_ssse/pre --post test/sha_naive_to_ssse/post --p1 test/sha_naive_to_ssse/p1 --p1lang asm --p2 test/sha_naive_to_ssse/p2 --p2lang asm --verif_mode hybrid --no_alias_analysis


#ChaCha20
echo "BENCHMARK: Verifying ChaCha20 implementation"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/asm --p2lang asm  --verif_mode hybrid --no_alias_analysis

#ChaCha20_ssse3
echo "Expected result: Equivalent (Time: )"
echo "BENCHMARK: Verifying ChaCha20 ssse3 implementation"
time python3 main.py --pre test/ChaCha20_ssse3/pre --post test/ChaCha20_ssse3/post --p1 test/ChaCha20_ssse3/dsl --p1lang dsl --p2 test/ChaCha20_ssse3/asm --p2lang asm --verif_mode hybrid --no_alias_analysis

#ChaCha20_naive_to_ssse
echo "Expected result: Equivalent (Time: )"
echo "BENCHMARK: Verifying equivalence between ChaCha20 algorithm and ChaCha20 with SSSE3 extension"
time python3 main.py --pre test/ChaCha20_naive_to_ssse/pre --post test/ChaCha20_naive_to_ssse/post --p1 test/ChaCha20_naive_to_ssse/p1 --p1lang asm --p2 test/ChaCha20_naive_to_ssse/p2 --p2lang asm --verif_mode hybrid --no_alias_analysis

#AES_encrypt
echo "Expected result: Equivalent (Time: )"
echo "BENCHMARK: Verifying AES128 encryption using 8-bit memory"
time python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/asm --p2lang asm --mem_model 8 --verif_mode hybrid --no_alias_analysis

#AES_decrypt
echo "BENCHMARK: Verifying AES128 decryption using 8-bit memory"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/AES_decrypt/pre --post test/AES_decrypt/post --p1 test/AES_decrypt/dsl --p1lang dsl --p2 test/AES_decrypt/asm --p2lang asm --mem_model 8 --verif_mode hybrid --no_alias_analysis

#AES_encrypt_key_expansion
echo "BENCHMARK: Verifying AES128 encryption key expansion using 8-bit memory"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/AES_encrypt_key_expansion/pre --post test/AES_encrypt_key_expansion/post --p1 test/AES_encrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_encrypt_key_expansion/asm --p2lang asm --mem_model 8 --verif_mode hybrid --no_alias_analysis

#AES_decrypt_key_expansion
echo "BENCHMARK: Verifying AES128 decryption key expansion using 8-bit memory"
echo "Expected result: Equivalent (Time: )"
time python3 main.py --pre test/AES_decrypt_key_expansion/pre --post test/AES_decrypt_key_expansion/post --p1 test/AES_decrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_decrypt_key_expansion/asm --p2lang asm --mem_model 8 --verif_mode hybrid --no_alias_analysis
