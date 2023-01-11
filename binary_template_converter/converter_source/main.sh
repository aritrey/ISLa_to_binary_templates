# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


if [ "$ENV" = "converter" ]; then
    python3 convert.py
else
    pip3 install py010parser six intervaltree
    python3 -O testing/main_tests.py
fi