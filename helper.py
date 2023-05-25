#!/bin/python3
import errno
import os
import signal
import functools

VERBOSE = 0
class R():#Regular Expression Snippet
    word = r'\w+'
    sep = r'\s+'
    sep0 = r'\s*'
    lparen0i = r'[\(]*'
    rparen0i = r'[\)]*'
    start = r'^'+sep0

def dis_duplicate(l):
    s = set()
    for i in l:
        s.add(i)
    return list(s)

def list1orEmptyList(l):
    if len(l)>0:
        return l[0]
    else:
        return []

def getMiddle(s,pre,suf):
    pos1 = s.find(pre)+len(pre)
    pos2 = s.find(suf,pos1)
    if pos1-len(pre) == -1 or pos2 == -1:
        return s
    return s[pos1:pos2]

def empty(l:list):
    return len(l) == 0

DEFAULT = '\033[0m'
red = lambda s:'\033[0;31m'+s+DEFAULT
green = lambda s:'\033[0;32m'+s+DEFAULT
yellow = lambda s:'\033[0;33m'+s+DEFAULT
blue = lambda s:'\033[0;34m'+s+DEFAULT
def error(s):
    print(red(s))
    exit(1)

def warn(s):
    print(yellow(s))

def str_cut_until(s:str,delim):
    return s[s.find(delim):] if s.find(delim)>-1 else ''

def concentrate(x,y):
    return x+y

class TimeoutError(Exception):
    pass

def timeout(seconds=10, error_message=os.strerror(errno.ETIME)):
    #thread unsafe
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result

        return wrapper

    return decorator

class Sequence():
    def __init__(s,prefix):
        s.idx = 0
        s.prefix = prefix
    def __next__(s):
        s.idx += 1
        return '"'+s.prefix+str(s.idx)+'"'

def removeStr(f):
    inQuote = False
    escape = False
    rst = ''
    for ch in f:
        if not inQuote:
            if not escape and ch == '"':
                inQuote = True
            else:
                rst += ch
        else:
            if not escape and ch == '"':
                inQuote = False
        if ch == '\\':
            escape = True
        else:
            escape = False
    return rst

mk_tid = lambda i: f"p{i}"
mk_tdecl = lambda tid,ln: f"{tid} = {ln}."

str_ = lambda s:f'"{s}"'
prob_choice = lambda p,a,b: a if random.random()<p else b
wrapParen = lambda l:[f"({i})"for i in l]
