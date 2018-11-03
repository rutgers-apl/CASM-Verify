echo "Buggy mutation #1: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm1 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #2: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm3 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #3: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm4 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #4: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/diffInst/pre5 --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm5 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #5: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm6 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #6: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm7 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #7: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm8 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #8: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm9 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #9: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm1 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #10: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm3 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #11: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm8 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #12: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm9 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #13: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm10 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #14: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm11 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #15: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm12 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #16: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm13 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #17: SHA256"
echo "Expected Result - Not Equivalent"
time python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm14 --p2lang asm --arch x86_64  --verif_mode hybrid

echo "Buggy mutation #18: AES128 encrypt"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm1 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #19: AES128 encrypt"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm2 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #20: AES128 encrypt"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm3 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #21: AES128 encrypt"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm5 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #22: AES128 encrypt key expansion"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_encrypt_key_expansion/pre --post test/AES_encrypt_key_expansion/post --p1 test/AES_encrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_encrypt_key_expansion/diffInst/asm2 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #23: AES128 encrypt key expansion"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_encrypt_key_expansion/pre --post test/AES_encrypt_key_expansion/post --p1 test/AES_encrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_encrypt_key_expansion/diffInst/asm3 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #24: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm1 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #25: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm3 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #26: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm4 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #27: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm5 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #28: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm6 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #29: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm10 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #30: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm11 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #31: AES128 decrypt key expansion - permute phase"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm12 --p2lang asm --arch x86_64 --verif_mode hybrid --mem_model 8

echo "Buggy mutation #32: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm1 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #33: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm2 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #34: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm3 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #35: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm4 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #36: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm5 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #37: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm6 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #38: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm7 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #39: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm8 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #40: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm9 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #41: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm10 --p2lang asm --verif_mode hybrid

echo "Buggy mutation #42: ChaCha20"
echo "Expected Result - Not Equivalent"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm11 --p2lang asm --verif_mode hybrid
