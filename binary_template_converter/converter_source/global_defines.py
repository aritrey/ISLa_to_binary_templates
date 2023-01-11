# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


import hashlib
import json


class GlobalDefines:
    TERMINAL = "terminal"
    NON_TERMINAL = "non_terminal"
    ISLA_RULE = "isla_rule"
    EPSILON=""
    STANDARD_PREF_POSSIBILITY=0

    @staticmethod
    def normalize(token, label):
        # creates a unique identifier for a labeled token.
        token_alnum = filter(str.isalpha, token)
        label_alnum = filter(str.isalpha, label)
        alnum_filter = "".join(token_alnum) + "_" + "".join(label_alnum)
        h = hashlib.sha256()
        h.update((token + label).encode("utf-8"))
        return f'{"".join(alnum_filter).upper()}_{h.hexdigest()[0:6].upper()}'

    @staticmethod
    def contained_in_set(uid, s):
        for e in s["data"]:
            if e["uid"] == uid:
                return True
        return False

    @staticmethod
    def hash_rule(rule):
        string = json.dumps(rule)
        h = hashlib.sha256()
        h.update(string.encode("utf-8"))
        return f'rule_{h.hexdigest()[0:24].upper()}'
