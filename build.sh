#!/bin/sh


# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


echo 'Building base image for BTMeetsCFG ...'
docker build -t norm/fuzzer-base-image - < base-image.dockerfile
echo 'Done!'
echo 'You can now run docker-compose up!'