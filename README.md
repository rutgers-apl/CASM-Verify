# CASM_Verify
CASM_Verify is a tool that automatically checks the equivalence of highly optimized assembly implementation of cryptographic algorithms against a reference implementation. The reference implementation can be another assembly implementation, or an implementation written in our DSL.


## Prerequisite
CASM_Verify requires python3 and the z3 bindings for python3. In ubuntu, the requirements can be installed using the following commands:
```bash
$ sudo apt-get install python3 python3-pip
$ sudo python3 -m pip install z3-solver
```
In macOS, use homebrew instead of apt-get:
```bash
$ brew install python3
$ sudo python3 -m pip install z3-solver
```

To install [z3](https://github.com/Z3Prover/z3) manually instead of using python package manager, follow the instruction in the link provided: [z3](https://github.com/Z3Prover/z3)


## Installation

### Installation using Docker
The simplest way to install CASM_Verify is to use the Docker Makefile provided in the repo. The makefile automatically installs all pre-requisite softwares.

1) Install Docker: Docker provides easy to follow documentation on how to install Docker on various platforms. You can find the instruction for your specific OS by going to https://docs.docker.com/, on the left sidebar, go to "Get Docker" -> "Docker CE" and click the OS for your machine.

2) Build Docker image: You can create docker image for CASM_Verify by typing the following command in the terminal,
```bash
docker build -t casmverify github.com/jpl169/CASM_Verify_Artifact
```

3) Run casmverify image: To run the docker image, type,
```bash
docker run -it casmverify
```

### Manual Installation
To manually install CASM-Verify, install the prerequisites, and clone this repository:
```bash
git clone https://github.com/rutgers-apl/CASM-Verify.git
```
Now you're ready to use CASM-Verify.


## CASM-Verify Benchmarks.
We provide a number of examples (used in our paper) in the "test" folder. We also provide a bash script that automatically runs the verification of these examples:
```bash
./Test1_benchmark.sh
```

## Usage
For the rest of the readme, we will be using the example in test/sha2rnd unless otherwise specified.

To verify the assembly implementation(test/sha2rnd/asm) using CASM-Verify, use the following command:
```bash
python3 main.py --pre test/sha2rnd/pre --post test/sha2rnd/post --p1 test/sha2rnd/dsl --p1lang dsl --p2 test/sha2rnd/asm --p2lang asm --mem-model 32
```
There are seven important parameters:
  1) --p1: specifies the file path to the reference implementation.
  2) --p1lang: specifies whether the reference implementation is written in x86_64 assembly (asm) or in our DSL (dsl).
  3) --p2: specifies the file path to the target implementation.
  4) --p2lang: specifies whether the target implementation is written in x86_64 assembly (asm) or in our DSL (dsl).
  5) --pre: File containing the precondition that specifies the program state at the beginning of p1 and p2.
  6) --post: File containing the postcondition that specifies which variables have to be equivalent for p1 and p2 to be equivalent.
  7) --mem-model: specifies how to model the memory. We currently either model the memory as an array of 8-bit values (8) or as an array of 32-bit values (32) for implementations that read/write word-sized values. This parameter is used for translating assembly implementation to our internal DSL.

The above example (test/sha2rnd) verifies an assembly implementation against the reference implementation written in our DSL, using a 32-bit value memory model.

We also provide an example that verifies an assembly implementation (ChaCha20 in x86_64 with SSE) against another assembly implementation (ChaCha20 in x86_64) in test/ChaCha20_naive_to_ssse:
```bash
python3 main.py --pre test/ChaCha20_naive_to_ssse/pre --post test/ChaCha20_naive_to_ssse/post --p1 test/ChaCha20_naive_to_ssse/p1 --p1lang asm --p2 test/ChaCha20_naive_to_ssse/p2 --p2lang asm --mem-model 32
```
and an example that uses an 8-bit value memory model in test/AES_decrypt:
```bash
python3 main.py --pre test/AES_decrypt/pre --post test/AES_decrypt/post --p1 test/AES_decrypt/dsl --p1lang dsl --p2 test/AES_decrypt/asm --p2lang asm --mem_model 8
```

## Domain Specific Language (DSL)
We provide an imperative C-like DSL to write the reference implementation, precondition, and the postcondition. We are actively refining our DSL to be more user friendly. To illustrate the features of our DSL, here is a code snippet of test/sha2rnd/dsl:
```
function SIGMA0(a) {
return (a >>> 2) ^ (a >>> 13) ^ (a >>> 22);
}
function CH(x, y, z) {
return (x & y) ^ (!x & z);
}
...

for (i from 0 to 1) {
	w[i] = m[i];
	sigma1 = SIGMA1(e);
	ch = CH(e,f,g);
	t1 = h + sigma1 + ch + k[i] + w[i];
...
}
```
`Variables (i.e. a)`: All variables are implicitly declared and they are integers. By default, they are 32-bit integers. If you need a different sized integers, use the format var:size, i.e. x:64 is a 64-bit integer named x. Constants are defaulted to 32-bit integers. Similar to variables, you can declare different sizes of constants, i.e. 1553:40 is a 40-bit integer representing the value 1553.
`Arrays (i.e. w[i])`: Like variables, arrays use 32-bit indices and hold 32-bit values by default. If you need different sized arrays, use the format name:s1\[index:s2\], i.e. mem:8\[addr:64\] is an array named mem, which uses 64-bit indices and returns 8-bit values.
`Loops`: Our DSL only allows a fixed-iteration for loop. CASM-verify internally unroll the for loop.
`Function`: our DSL supports mathematical functions. CASM-verify internally inlines the function.

## Precondition
