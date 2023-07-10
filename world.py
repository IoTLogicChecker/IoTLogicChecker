#!/bin/python3
from copy import deepcopy
from helper import *
from assumptionManager import FormSpace
from userActionEnumerator import DecisionState
from logicDeductor import sendNewDeclares,deriveSingleForm,deriveSingleFormsEternal,deriveFormPairs

def stripTime(op):
    return int(''.join(op.split('at')[:-1]).strip())
class World:
    def __init__(s,twelf):
        s._time = 5
        s.seqGen = Sequence('randomstr')
        s.FS = FormSpace(twelf)
        s.DS = DecisionState()
        s.PS = set()#Security Problems
        s.level = 0
        s.twelf = twelf
    def __copy__(s):
        cls = s.__class__
        result = cls.__new__(cls)
        result.__dict__.update(s.__dict__)
        return result
    def __deepcopy__(s,memo):
        cls = s.__class__
        result = cls.__new__(cls)
        memo[id(s)] = result
        for k, v in s.__dict__.items():
            if k != 'twelf':#shallow copy twelf
                setattr(result, k, deepcopy(v, memo))
            else:
                setattr(result, k, v)
        return result

    def time(s):
        return s._time

    def timePass(s,t=None):
        if not t:
            s._time += 5
        elif t <= s._time:
            #print(f'{t} not bigger than {s._time}, OMMIT')
            return #time not add, pass
        else:
            #print(f'time add at {t}')
            s._time = t
        for tid in s.FS.avail_tids():
            decl = s.FS.D[tid]
            if decl.checkOperation():
                s.FS.turnOff(decl)
                print(f'time pass turn off {decl}')
        #print(f'----------time:{s._time}----------')

    def init(s):
        sendNewDeclares(s)
        deriveSingleFormsEternal(s)

    def step(s,op,giveTime):
        newworld = deepcopy(s)
        newworld.level += 1
        if giveTime:
            t = findTimes(op)
            print(t)
            newworld.timePass(t)
        else:
            newworld.timePass()
        tid = newworld.FS.add(op,operationp=True)
        newworld.DS.trace(op)
        s.twelf.decl(newworld.FS.useDecl(tid))
        deriveSingleForm(newworld,tid)
        while not newworld.FS.reach_fixpoint():
            sendNewDeclares(newworld)
            deriveFormPairs(newworld)
        return newworld
