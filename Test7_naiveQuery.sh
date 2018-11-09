bold=$(tput bold)
normal=$(tput sgr0)

echo "${bold}Verifying Benchmark using Naive Single Query Method.${normal}"
echo "${bold}10 benchmarks total.${normal}"
echo "${bold}Total Expected Required Time: 120 hours!${normal}"
echo ""


#SHA256
echo "${bold}BENCHMARK: SHA${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/asm --p2lang asm
echo ""

#SHA256 with SSSE3
echo "${bold}BENCHMARK: SHA-SSE${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/asm --p2lang asm
echo ""

#sha_naive_to_ssse
echo "${bold}BENCHMARK: SHA-EQUIV${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/sha_naive_to_ssse/pre --post test/sha_naive_to_ssse/post --p1 test/sha_naive_to_ssse/p1 --p1lang asm --p2 test/sha_naive_to_ssse/p2 --p2lang asm
echo ""

#ChaCha20
echo "${bold}BENCHMARK: CHACHA${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/asm --p2lang asm
echo ""

#ChaCha20_ssse3
echo "${bold}BENCHMARK: CHACHA-SSE${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/ChaCha20_ssse3/pre --post test/ChaCha20_ssse3/post --p1 test/ChaCha20_ssse3/dsl --p1lang dsl --p2 test/ChaCha20_ssse3/asm --p2lang asm
echo ""

#ChaCha20_naive_to_ssse
echo "${bold}BENCHMARK: CHACHA-EQUIV${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/ChaCha20_naive_to_ssse/pre --post test/ChaCha20_naive_to_ssse/post --p1 test/ChaCha20_naive_to_ssse/p1 --p1lang asm --p2 test/ChaCha20_naive_to_ssse/p2 --p2lang asm
echo ""

#AES_encrypt
echo "${bold}BENCHMARK: AES-ENC${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/asm --p2lang asm --mem_model 8
echo ""

#AES_decrypt
echo "${bold}BENCHMARK: AES-DEC${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/AES_decrypt/pre --post test/AES_decrypt/post --p1 test/AES_decrypt/dsl --p1lang dsl --p2 test/AES_decrypt/asm --p2lang asm --mem_model 8
echo ""

#AES_encrypt_key_expansion
echo "${bold}BENCHMARK: AES-KEY-ENC${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/AES_encrypt_key_expansion/pre --post test/AES_encrypt_key_expansion/post --p1 test/AES_encrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_encrypt_key_expansion/asm --p2lang asm --mem_model 8
echo ""

#AES_decrypt_key_expansion
echo "${bold}BENCHMARK: AES-KEY-DEC${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~12 hours${normal}"
time python3 naiveQuery.py --pre test/AES_decrypt_key_expansion/pre --post test/AES_decrypt_key_expansion/post --p1 test/AES_decrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_decrypt_key_expansion/asm --p2lang asm --mem_model 8
