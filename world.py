#!/bin/python3
from copy import deepcopy
from helper import *
from assumptionManager import FormSpace
from userActionEnumerator import DecisionState
from logicDeductor import sendNewDeclares,deriveSingleForm,deriveSingleFormsEternal,deriveFormPairs

class World:
    def __init__(s,twelf):
        s.time = 0
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

    def timePass(s):
        s.time += 5
        for tid in s.FS.avail_tids():
            decl = s.FS.D[tid]
            if decl.checkOperation():
                s.FS.turnOff(decl)
        #print(f'----------time:{s.time}----------')

    def init(s):
        sendNewDeclares(s)
        deriveSingleFormsEternal(s)

    def step(s,op):
        newworld = deepcopy(s)
        newworld.level += 1
        newworld.timePass()
        tid = newworld.FS.add(op,operationp=True)
        newworld.DS.trace(op)
        s.twelf.decl(newworld.FS.useDecl(tid))
        deriveSingleForm(newworld,tid)
        while not newworld.FS.reach_fixpoint():
            sendNewDeclares(newworld)
            deriveFormPairs(newworld)
        return newworld
