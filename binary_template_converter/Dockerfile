# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


FROM norm/fuzzer-base-image

# install dependencies
RUN apt install -y git g++ make automake python3-pip zlib1g-dev libboost-dev
RUN pip3 install py010parser six intervaltree Jinja2 matplotlib

# build format fuzzer
RUN git clone https://github.com/uds-se/FormatFuzzer.git
WORKDIR /FormatFuzzer
RUN touch configure Makefile.in
RUN ./configure

# run the converter
WORKDIR /converter
ADD converter_source/ .

ARG ENV
ENV ENV=$ENV
ENTRYPOINT [ "bash", "main.sh"]