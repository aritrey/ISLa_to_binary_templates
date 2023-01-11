#!/bin/sh
rm -rf output
mkdir output
docker build -t "bachelor-proposal_converter:latest" ./binary_template_converter
docker compose up --build tests #run only service "converter"