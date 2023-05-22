#!/bin/python3
import sys
from interface import Twelf
from helper import *
from world import World
from userActionEnumerator import UserActionEnumerator
from logicDeductor import initLogic,readPolicy,checkViolations,checkNoSatisfy,summary

STEP = False
#STEP = True
policy_path = './policy.txt'

def run(twelf, mode=3):
    global policy_path
    if len(sys.argv)>1:
        policy_path = sys.argv[1]
        print('use ',policy_path)

    initLogic(twelf)
    w0 = World(twelf)
    AE = UserActionEnumerator(w0,twelf,mode)
    policy = readPolicy(policy_path)
    policy.load(twelf,w0,AE)
    w0.init()
    AE.simulate()
    w = w0
    try:
        while True:
            if op := AE.gen():
                print(op)
                w = w.step(op)
                AE.setWorld(w)
            else:
                break
            if mode == 2:
                if checkViolations(w):
                    break
            if STEP:
                #step debug
                FS.show()
                input('Next round?')
    except KeyboardInterrupt:
        print(yellow('stop'))
    checkViolations(w)
    checkNoSatisfy(w)
    summary(w,AE,True)

if __name__ == '__main__':
    twelf = Twelf()
    run(Twelf())
    twelf.quit()
