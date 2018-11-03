FROM ubuntu:18.04

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update
RUN apt-get install -yq --no-install-recommends apt-utils 
RUN apt-get install -yq python3 python3-pip jgraph
RUN python3 -m pip install z3-solver

WORKDIR /home

ADD CASM_Verify.tar /home

WORKDIR /home/CASM_Verify