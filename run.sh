#!/bin/sh

# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


rm -rf output
mkdir output
docker build -t "bachelor-proposal_converter:latest" ./binary_template_converter
docker compose up --build converter #run only service "converter"