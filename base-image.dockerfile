# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


FROM ubuntu:22.04

RUN apt update
RUN apt -y upgrade
RUN apt install -y python3-dev python3-pip git

# Verify python3 was successfully installed and is version 3.10
RUN python3 -V

# Offical installation instructions. https://www.fuzzingbook.org/html/Importing.html
RUN pip3 install fuzzingbook
RUN pip install isla-solver