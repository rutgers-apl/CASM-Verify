#ChaCha20
echo "BENCHMARK: Verifying ChaCha20 implementation"
echo "Expected result: Equivalent (Time: )"
python3 main.py --pre test/sha2rnd/pre --post test/sha2rnd/post --p1 test/sha2rnd/dsl --p1lang dsl --p2 test/sha2rnd/asm --p2lang asm  --verif_mode hybrid


#ChaCha20
echo "BENCHMARK: Verifying ChaCha20 implementation"
echo "Expected result: Equivalent (Time: )"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/asm --p2lang asm  --verif_mode hybrid

#Part of AES128 key expansion for decryption algorithm
echo "BENCHMARK: Verifying AES key expansion permutation"
echo "Expected result: Equivalent (Time: )"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/asm --p2lang asm  --verif_mode hybrid

#AES_decrypt
echo "BENCHMARK: Verifying AES128 decryption using 8-bit memory"
echo "Expected result: Equivalent (Time: )"
python3 main.py --pre test/AES_decrypt/pre --post test/AES_decrypt/post --p1 test/AES_decrypt/dsl --p1lang dsl --p2 test/AES_decrypt/asm --p2lang asm --mem_model 8 --verif_mode hybrid

#AES_encrypt
echo "Expected result: Equivalent (Time: )"
echo "BENCHMARK: Verifying AES128 encryption using 8-bit memory"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/asm --p2lang asm --mem_model 8 --verif_mode hybrid
