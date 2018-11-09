# CASM_Verify_Artifact

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

