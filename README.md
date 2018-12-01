# CASM_Verify
CASM_Verify is a tool that automatically checks the equivalence of highly optimized assembly implementation of cryptographic algorithms against a reference implementation. The reference implementation can be another assembly implementation, or an implementation written in our DSL.

## Installation
The simplest way to install CASM_Verify is to use the Docker Makefile provided in the repo.

### How to install Docker
Docker provides easy to follow documentation on how to install Docker on various platforms. You can find the instruction for your specific OS by going to https://docs.docker.com/, on the left sidebar, go to "Get Docker" -> "Docker CE" and click the OS for your machine.

### How to build CASM_Verify Docker Image
You can create docker image for CASM_Verify by typing the following command in the terminal:
```bash
docker build -t casmverify github.com/jpl169/CASM_Verify_Artifact
```

To run docker image, type:
```bash
docker run -it casmverify
```

## Testing benchmarks
We provide bash scripts that automatically runs the command to test CASM_Verify's benchmarks. Since running all CASM_Verify's benchmarks will take well over 24 hours, we divided the entire test cases into small sections.

Before executing each benchmark, the scripts will print which test
case it's running and the expected output: Whether (1) p1 is
equivalent to p2, (2) p1 is not equivalent to p2. **If CASM_Verify
experiences SMT Solver timeout, it will report that p1 is not
equivalent to p2, but also output that it experiences SMT Solver
timeout.**

If you would like to skip any of the benchmarks in the script, you can
press ctrl + c to stop the current benchmark and run the next benchmark.

### 0. Micro (Fast) Benchmarks.
This script contains four benchmarks for quickly testing whether CASM_Verify can correctly verify that an implementation is correct. Estimated time required : ~36 minutes
```bash
./Test0_fastBenchmark.sh
```

### 1. OpenSSL Benchmarks with full features of CASM_Verify.
This experiment tests whether the assembly implementation of cryptographic algorithms found in OpenSSL is correct. This benchmark is equivalent to the Table 1 in Evaluation Section, or the fourth bar in Figure 6. Estimated time required : ~10 hours 30 minutes
```bash
./Test1_benchmark.sh
```

### 2. OpenSSL Benchmarks with only Node Merging.
This experiment is similar to Test1, but only uses the Node Merging feature. This is equivalent to the second bar shown in Figure 6. Estimated time required : ~4 hours 20 minutes
```bash
./Test2_nodeMergeOnly.sh
```

### 3. OpenSSL Benchmarks with QuickCheck.
This experiment is similar to Test 1, but uses QuickCheck without Memory Optimization. This is equivalent to the third bar shown in Figure 6. Estimated time required : ~6 hours 21 minutes
```bash
./Test3_quickCheck.sh
```

### 4. Buggy Implementations with Common Developer Mistakes.
This experiment contains benchmarks with buggy implementations with mistakes that developers can make. Estimated time required : ~25 minutes
```bash
./Test4_developMistakeBug.sh
```

### 5. Hard to detect Bug
This experiment contains benchmarks with buggy implementations, where
random input testing may not be able to detect the bug. Estimated time
required : ~18 hours 15 minutes
```bash
./Test5_hardToFindBug.sh
```

### 6. Equivalent Implementations
This experiment contains benchmarks that are mutated from OpenSSL implementations, but is still semantically correct. Estimated time required : ~4 hours 20 minutes
```bash
./Test6_additionalEquivalenceTest.sh
```

### 7. Single Query Benchmark
This experiment tries to verify the functional correctness of assembly code by creating one large SMT Query instead of using CASM_Verify. Estimated time required : ~120 hours
```bash
./Test7_naiveQuery.sh
```







