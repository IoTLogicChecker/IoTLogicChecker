#!/bin/python3
from helper import *
import signal
from time import sleep
import os
from subprocess import Popen,PIPE,run
from config import *

CONFIG_PATH = './sources.cfg'
@timeout(5)
def readUntil(ch,keywords:'list of str'):
    msg = b''
    while True:
        msg += ch.read(1)
        if VERBOSE >= 2:
            print(red('[DEBUG]'),msg)
        for i,kw in enumerate(keywords):
            if msg.endswith(kw.encode('utf-8')):
                if VERBOSE >= 1:
                    warn(msg.decode('utf-8'))
                return i,msg.decode('utf-8')

def getChildProcess(pid):
    ps_output = run(['ps', '-opid', '--no-headers', '--ppid', str(pid)],
                stdout=PIPE, encoding='utf8')
    child_process_ids = [int(line) for line in ps_output.stdout.splitlines()]
    return child_process_ids

class Twelf():
    def __init__(s):
        s.twelf = Popen([TWELF_PATH],stdin = PIPE, stdout = PIPE)
        #s.childs = [s.twelf.pid+1]
        sleep(0.1)
        s.childs = getChildProcess(s.twelf.pid)

    def restart(s):
        s.quit()
        s.twelf = Popen([TWELF_PATH],stdin = PIPE, stdout = PIPE)
        #s.childs = [s.twelf.pid+1]
        sleep(0.1)
        s.childs = getChildProcess(s.twelf.pid)

    def read(s):
        OK = '%% OK %%\n'
        ABORT = '%% ABORT %%\n'
        keywords = [OK,ABORT]
        try:
            r,m = readUntil(s.twelf.stdout,keywords)
        except TimeoutError:
            s.interrupt_top()
            warn('time out at read, iterrupt it')
            return False
        s.twelf.stdout.flush()
        if r == 0:return True
        else:
            warn(m)
            return False

    def rawwrite(s,msg):
        s.twelf.stdin.write((msg+'\n').encode('utf-8'))

    def write(s,msg):
        s.twelf.stdin.flush()
        s.twelf.stdin.write((msg+'\n').encode('utf-8'))
        s.twelf.stdin.flush()

    def interact(s):
        OK = '%% OK %%\n'
        ABORT = '%% ABORT %%\n'
        keywords = [OK,ABORT]
        while True:
            cmd = input('>').strip()
            if cmd == 'q':
                break
            s.write(cmd)
            r,m = readUntil(s.twelf.stdout,keywords)
            s.twelf.stdout.flush()
            print(blue(m))
            print(r)

    def silent(s): 
        s.write('set chatter 2')
        return s.read()

    def verbose(s): 
        s.write('set chatter 3')
        return s.read()

    def quit(s):
        s.rawwrite('quit')
        #s.twelf.wait()

    def kill(s):
        s.twelf.kill()

    def config(s):
        s.write(f'Config.read {CONFIG_PATH}')
        return s.read()

    def load(s):
        s.write('Config.load')
        return s.read()

    def reset(s):
        s.write('reset')
        return s.read()

    def decl(s,decl):
        s.write('readDecl')
        s.write(decl)
        if not s.read():
            print(red(f'[E] twelf declaration abort when handle {decl}'))
            s.quit()
            #FS.show()
            print('into interact mode to debug')
            s.interact()
            exit(2)

    def interrupt(s,pid):
        try:
            os.kill(pid,signal.SIGINT)
        except PermissionError as e:
            print(e)
            print(os.system(f'kill -2 {pid}'))
        return s.read()#find ok

    def interrupt_top(s):
        return s.interrupt(s.childs[0])#!pid+1 is his "top" process

    def query(s,query,cb=lambda f:[f])->list:
        s.write('top')
        KW_ques = '?- '
        readUntil(s.twelf.stdout,[KW_ques])
        s.write(query)
        ans = []
        while True:
            r,m = readUntil(s.twelf.stdout,['More? ',KW_ques])
            if r == 0:
                delim = 'ANS ='
                m = str_cut_until(m,delim)
                form = m.lstrip(delim).rstrip('.\nMore? ')
                ans += cb(form)
                s.write('y')
                continue
            else:#when no more solutions
                if 'error found' in m:
                    #FS.show()
                    s.kill()
                    error(f'[-] {m} in {query}')
                    exit(1)
                s.interrupt_top()
                return ans

if __name__ == '__main__':
    t = Twelf()
    t.config(CONFIG_PATH)
    t.load()
    print(t.decl("p1 = foo."))
    t.quit()
