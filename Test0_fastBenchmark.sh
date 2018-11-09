bold=$(tput bold)
normal=$(tput sgr0)

echo "${bold}Testing on Small Benchmarks.${normal}"
echo "${bold}4 benchmarks total.${normal}"
echo "${bold}Total Expected Required Time: ~36 minutes.${normal}"
echo ""

#2 rounds of SHA256
echo "${bold}BENCHMARK: Verifying 2 rounds of SHA256${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/sha2rnd/pre --post test/sha2rnd/post --p1 test/sha2rnd/dsl --p1lang dsl --p2 test/sha2rnd/asm --p2lang asm  --verif_mode hybrid
echo ""

#ChaCha20
echo "${bold}BENCHMARK: Verifying ChaCha20 implementation${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~ 5 minutes${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/asm --p2lang asm  --verif_mode hybrid
echo ""

#AES_decrypt
echo "${bold}BENCHMARK: Verifying AES128 decryption using 8-bit memory${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~ 14 minutes${normal}"
python3 main.py --pre test/AES_decrypt/pre --post test/AES_decrypt/post --p1 test/AES_decrypt/dsl --p1lang dsl --p2 test/AES_decrypt/asm --p2lang asm --mem_model 8 --verif_mode hybrid
echo ""

#AES_encrypt
echo "${bold}BENCHMARK: Verifying AES128 encryption using 8-bit memory${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~ 17 minutes${normal}"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/asm --p2lang asm --mem_model 8 --verif_mode hybrid
echo ""
