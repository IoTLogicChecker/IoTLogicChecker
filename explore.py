#!/bin/python3
import sys
import re
from time import sleep
from world import World
from userActionEnumerator import UserActionEnumerator
from logicDeductor import readPolicy,initLogic,checkViolations,checkNoSatisfy,summary,sendAvailableLemmaDeclares,sendAvailableDeclares
from interface import Twelf
from helper import *
from threading import Thread
policy_path = 'case/iRobot.txt'
ToErrorFilePath = lambda fp:fp.split('/')[-1]+'.log'
twelf = Twelf()
if len(sys.argv)>1:
    policy_path = sys.argv[1]
    print('[+] Use ',policy_path)

def load(w,policy_path,AE):
    initLogic(twelf)
    policy = readPolicy(policy_path)
    policy.load(twelf,w,AE)
    w.init()
    AE.simulate()
    return policy

def reload(policy,w):
    twelf.reset()
    twelf.load()
    sleep(0.05)
    policy.loadUserDefineTypes(twelf)
    sendAvailableDeclares(w)

def restart(policy,w0):
    twelf.quit()
    twelf.restart()
    twelf.read()
    sleep(0.05)
    twelf.config()
    twelf.load()
    sleep(0.05)
    #twelf.interact()
    policy.loadUserDefineTypes(twelf)
    sendAvailableDeclares(w0)

def logErrorToFile(ErrorWorlds):
    fp = ToErrorFilePath(policy_path)
    with open(fp,'w') as f:
        for i,errorw in enumerate(ErrorWorlds):
            f.write(f'======Error {i}=========\n')
            for op in errorw.DS.traceOpSeq:
                f.write(op+'\n')
            for p in errorw.PS:
                f.write(p+'\n')
            f.write('\n')
    print(f'[+] Write error to {fp}')

def noUserMoveAfter(case,level):
    for i in range(level+1,len(case)):
        if case[i] == 'user':
            return False
    return True

ErrorWorlds = []
w0 = World(twelf)
AE = UserActionEnumerator(w0,twelf)
#World.step : deepcopy then step to new world
policy = load(w0 , policy_path, AE)
cnt = 0
def filter_operation(w,op,AE):
    ifpass = False
    if not empty(w.DS.traceOpSeq):
        lastop = w.DS.traceOpSeq[-1]
        prin = lastop.split(' ')[0].strip()
        if prin == 'user':
            prin = prin+' '+lastop.split(' ')[1].strip()
        if prin == 'user "C"' and AE.stripTime(op) == AE.stripTime(lastop):
            #jump the attacker repeated operation
            ifpass = True
    return ifpass
AE.show()
print('----------start----------')
cases = AE.whoMoveCombinations()
if not cases:
    print('No combinations')
    exit(1)
level_stop = len(cases[0])
print('stop at',level_stop)
for case in cases:
    print('\nNow the case:',case)
    #if case != ['user', 'attacker', 'user', 'attacker', 'user', 'attacker']:
    #    continue
    level_last = 0
    ws = [w0]
    #input('Stop every case')#DEBUG
    while not empty(ws):
        w = ws.pop()
        AE.setWorld(w)
        if w.level < level_last:
            reload(policy,w)
            #sendAvailableLemmaDeclares(w)#if level decrese, need to redeclare
        level_last = w.level
        if w.level < level_stop:
            choice = case[w.level]
            if choice == 'user':
                op = AE.getUserOperations(case,w.level)
                #if filter_operation(w,op,AE):
                #    continue
                nw = w.step(op)
                ws.append(nw)
            else:#attacker
                ops = AE.generateAllOperations()
                for op in ops:
                    #filter:speed up
                    if filter_operation(w,op,AE):
                        continue
                    
                    nw = w.step(op)
                    
                    if noUserMoveAfter(case, w.level):
                        if checkViolations(nw):
                            print(red('[+] Found!'))
                            checkNoSatisfy(nw)
                            ErrorWorlds.append(nw)
                            continue
                    ws.append(nw)
        else:#the end of level, check security
            cnt +=1
            print('\rNow:',cnt,' '*10,end='')
            sendAvailableLemmaDeclares(w)
            errorp = False
            if checkViolations(w):
                print(red('[+] Found!'))
                errorp = True
            if checkNoSatisfy(w):
                print(red('[+] Found!'))
                errorp = True
            if errorp:
                #summary(w,AE)
                ErrorWorlds.append(w)
    #reload(policy,w0)
    restart(policy,w0)

print(cnt)
twelf.quit()
logErrorToFile(ErrorWorlds)
