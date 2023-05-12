#!/bin/python3
from itertools import combinations
from functools import reduce,partial
from copy import deepcopy
import re
from interface import Twelf
from helper import *
import config
from logicDeductor import sendNewDeclares

class DecisionState():
    def __init__(s,t=0):
        s.time = t
        s.database = dict()#{'user "A"':set("$$$","password"),...}
        s.traceOpSeq = []
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
            setattr(result, k, deepcopy(v, memo))
        return result
    def trace(s,op):
        s.traceOpSeq.append(op)
        return op
    def checkKnows(s,decl):
        if tup:=decl.checkTransfer():
            P,S = tup
            P = P.strip()
            if P == 'user "C"': P = 'userC'
            elif P == 'user "A"': P = 'userA'
            try:
                S = eval(S)
            except:
                #print(S)
                return
            if ',' in P:
                P,S1 = P.split(',')
                P = P.strip()
                try:
                    S1 = eval(S1)
                except:
                    pass
                else:
                    s.knows(P,S1)
                    if P == 'user "C"': P = 'userC'
                    elif P == 'user "A"': P = 'userA'
            s.knows(P,S)
            return S

    def knows(s,prin,data):
        if prin not in s.database:
            s.database[prin] = set([data])
        else:
            s.database[prin].add(data)

    def show(s):
        print('------databse---------------')
        print(s.database)
        print('------trace-----------------')
        for op in s.traceOpSeq:
            print(op)


class UserActionEnumerator():
    def __init__(s,world,twelf,mode=3):
        s.UserOpSeq = []#queue
        s.UserOpSeq2 = []#stack
        s.mode = mode
        s.actions = []
        s.transfers = []
        s.cnt = 0
        s._loopcnt = 0
        s.world = world
        s.twelf = twelf
        if 'ATTACK_MOVE_NUM' in dir(config):
            s.attackMoveNum = config.ATTACK_MOVE_NUM
        else:
            s.attackMoveNum = None

    def simulateAction(s,l):
        actions = s.twelf.query(f'find-action ({" ^ ".join(l)}) ANS.')
        actions = dis_duplicate(actions)
        s.actions = actions
    
    def simulateTransfer(s,l):
        l = s.twelf.query(f'find-transfer ({" ^ ".join(l)}) ANS foo.')
        l = dis_duplicate(l)
        ans = {} 
        for i in l:
            pss = i.split(',')
            p = pss[0].strip()
            if p not in ans:
                ans[p] = set()
            ans[p].add(len(pss) - 1)
        s.transfers = ans

    def simulate(s):
        i = 0
        l = []
        for op in s.UserOpSeq:
            #write a parser to parse command
            #depend on principals to choose
            tid = f'tmp_{i}'
            l.append(tid)
            s.twelf.decl(f"{tid} = {op}.")
            i += 1
        sendNewDeclares(s.world)
        l += s.world.FS.avail_tids()
        s.simulateAction(l)
        s.simulateTransfer(l)

    def generateAllOperations(s):
        ops = []
        ops += [s.wrapTime(op) for op in s.genAttackerOps()]
        return ops
   
    def genAttackerOps(s):
        #ops = dis_duplicate(s.genTransfer()) + dis_duplicate(s.genSays())
        ops = s.genTransfer() + s.genSays()
        return ops
    
    def genTransfer(s):
        ops = []
        f = lambda x : lambda y : lambda d:f"{x} transfer ({y} , {d})"
        f2 = lambda x : lambda y : lambda d:f"{x} transfer ({y} , {d} , \"B\")"
        for p,v in s.transfers.items():
            if p != 'userC' or p != 'user "C"':#FUTURE TODO
                if 1 in v:
                    ops += s.genAllDatas('userC',s.listcallwith(p,s.genAttackerPrin([f])))
                if 2 in v:
                    ops += s.genAllDatas('userC',s.listcallwith(p,s.genAttackerPrin([f2])))

        return ops

    def listcallwith(s,v,fs):
        return [f(v) for f in fs]

    def genSays(s):
        f = lambda x:lambda a:f"{x} says (action ({a}))"
        return s.genAllActions(s.genAttackerPrin([f]))
    
    def genAllActions(s,fs):
        return [f(action) for f in fs for action in s.actions]

    def genAllDatas(s,p,fs):
        str_ = lambda s:f'"{s}"'
        if p in s.world.DS.database:
            return [f(str_(data)) for f in fs for data in s.world.DS.database[p]]
        else:
            return [f('"RandomStrBy%s"'% (p.replace('"',''))) for f in fs] #TODO

    def genAttackerPrin(s,fs):
        return s.listcallwith('userC',fs)

    def genAllPrins(s,fs,exclude=['userA','userC']):
        Prins = ['userA','userC',"cloud",'deviceB']
        if exclude:
            Prins = list(set(Prins).difference(set(exclude)))
        return [f(prin) for f in fs for prin in Prins]

    def genRandomly(s):
        cs = [lambda s:s=='user',lambda s:s=='attacker']
        case_ = random.choice(cs)
        if t := s.findNextUserOpTimes():
            if s.world.time > t:
                case_ = cs[0]#let user op goes first
        if case_('user'):
            if len(s.UserOpSeq)>0:
                op = s.UserOpSeq.pop()
                s.checkTimes(op)
                return w.DS.trace(op)
            else:
                if s.cnt > 0:
                    s.cnt -= 1
                    return s.attackerOperationRandomly()
        elif case_('attacker'):
            if s.cnt > 0:
                s.cnt -= 1
                return s.attackerOperationRandomly()
        return None
    def feedAsPolicy(s):
        if len(s.UserOpSeq)>0:
                op = s.UserOpSeq.pop()
                s.checkTimes(op)
                return op
        else:
            return None
    def gen(s)->'ln or None':
        if s.mode == 2:
            return s.genRandomly()        
        elif s.mode == 3:
            return s.feedAsPolicy() 
        elif s.mode == 4:
            return None
    def findNextUserOpTimes(s)->'int or None':
        for op in s.UserOpSeq[::-1]:
            if t := s.findTimes(op):
                return t
    def findTimes(s,op)->int:
        regexp = r'at\s+\(+\s*time\s*(\d+)\)+\s*[.]{0,1}\s*$'
        r = re.findall(regexp,op)
        if len(r)>0:
            return int(r[0])
    def checkTimes(s,op):
        if t:=s.findTimes(op):
            s.world.time = int(t)
            return t
    def setWorld(s,w):
        s.world = w
    def wrapTime(s,op,t=None):
        if not t:
            t = s.world.time
        return f'{op} at (time {t})'
    def stripTime(s,op):
        return ''.join(op.split('at')[:-1]).strip()
    def ifLocalAction(s,a):
        return 'button' in a
    def genOperationR(s,px=None,py=None):
        Ops = [s.genTransferR,s.genSaysR]
        return s.wrapTime(random.choice(Ops)(px,py))
    def userOperationRandomly(s): return s.genOperationR("userA")
    #def attackerOperation(s): return s.genOperation("userC")
    def attackerOperationRandomly(s,w):
        #me = 'user "C"'
        me = 'userC'
        if me in s.database and len(s.database[me])>0:
            return s.wrapTime(prob_choice(0.8,\
                    s.genTransferR(me,prob_choice(0.9,"cloud","deviceB")),\
                    s.genSaysR(me,prob_choice(0.7,"deviceB","cloud"))))
        else:
            return s.wrapTime(s.genSaysR(me,prob_choice(0.7,"deviceB","cloud")))
    def genTransferR(s,px=None,py=None,d=None):
        f = lambda x,y,d:f"{x} transfer ({y} , {d})"
        if not px:
            px = s.randomPrin()
        if not py:
            py = s.randomPrin([px])
        alphaset = [chr(i) for i in range(97,123)]
        alphaset += [chr(i) for i in range(97-32,123-32)]
        str_ = lambda s:f'"{s}"'
        d2 = prob_choice(0.9, "B" , "D")
        if px in s.transfers:
            cnt = random.choice(list(s.transfers[px]))
            if cnt == 2:
                f = lambda x,y,d:f"{x} transfer ({y} , {d} , {d2})"
        if not d:
            if px in s.database and len(s.database[px]) > 0:
                
                d = str_(random.choice(list(s.database[px])))
            else:
                d = str_(''.join([random.choice(alphaset) \
                             for i in range(random.choice(range(4,7)))]))
        return f(px,py,d)
    def genSaysR(s,px=None,py=None,att=None):
        f = lambda x,a:f"{x} says (action ({a}))"
        if not px:
            px = s.randomPrin("cloud")
        a = s.genActions(py,att)
        if s.world.time > 65:
            if s.ifLocalAction(a):
                return s.genTransferR(px,py)
            else:
                return f(px,a)
        else: 
            return f(px,a)
    def genActionsR(s,py,att):
        if len(s.actions) > 0:
            return random.choice(s.actions)
        else:
            if not att:
                att = s.randomAttribute()
            return f'(device "B") \'s {att}'
    def randomAttribute(s):
        #Attributes = ["button","local"]
        Attributes = ["button"]
        return random.choice(Attributes)
    def randomPrin(s,exclude=None):
        Prins = ['user "A"','user "C"',"cloud",'device "B"']
        if exclude:
            Prins = list(set(Prins).difference(set(exclude)))
        return random.choice(Prins)

    def addUserOp(s,op):
        s.UserOpSeq.insert(0,op)#queue
        s.UserOpSeq2.append(op)#stack
        s.cnt += 1
        return s


    def getUserOperations(s,case,level):
        level = level % len(case)
        n = 0
        for l,choice in enumerate(case):
            if l == level:
                return s.wrapTime(s.UserOpSeq2[n])
            if choice == 'user':
                n += 1

    def whoMoveCombinations(s):
        #N = len(s.UserOpSeq)*1#DEBUG
        if s.attackMoveNum:
            N = len(s.UserOpSeq)+s.attackMoveNum
        else:
            N = len(s.UserOpSeq)*2#default
        cases = []
        for combine in combinations(range(N),len(s.UserOpSeq)):
            case = ['attacker']*N
            for idx in combine:
                case[idx] = 'user'
            cases.append(case)
        return cases

    def show(s):
        print('======DecisionSpace=========')
        print('------simulate actions---------')
        print(s.actions)
        print('------simulate transfers---------')
        print(s.transfers)
        print('------left UserOpSeq--------')
        for uop in s.UserOpSeq:
            print(uop)
