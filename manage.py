#!/bin/python3
from itertools import combinations
from functools import reduce,partial
import os
import random
import re
import json
import time
import sys
import re
from interface import Twelf
from helper import *
from copy import deepcopy

STEP = False
#STEP = True
CONCISE = False
#four modes
#1:auto, user only need to provide "policy" to describe cloud/device access control rule.
#2:semi auto, provide "user operation sequence",enumerate attacker operation sequence.
#3:manual with state progress.
#4:manual in a static world.
RUN_MODE = 2

policy_path = './policy.txt'
VISUAL_RST_FILE = './visualize/data.js'

mk_tid = lambda i: f"p{i}"
mk_tdecl = lambda tid,ln: f"{tid} = {ln}."
prob_choice = lambda p,a,b: a if random.random()<p else b
wrapParen = lambda l:[f"({i})"for i in l]
twelf = Twelf()

class Sequence():
    def __init__(s,prefix):
        s.idx = 0
        s.prefix = prefix
    def __next__(s):
        s.idx += 1
        return '"'+s.prefix+str(s.idx)+'"'

class World:
    def __init__(s):
        s.time = 0
        s.seqGen = Sequence('randomstr')
        s.FS = FormSpace()
        s.DS = DecisionState()
        s.PS = set()#Security Problems
        s.level = 0
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
        twelf.decl(newworld.FS.useDecl(tid))
        deriveSingleForm(newworld,tid)
        while not newworld.FS.reach_fixpoint():
            sendNewDeclares(newworld)
            deriveFormPairs(newworld)
        return newworld

class Declaration:
    def __init__(s,tid,form,parents=set()):
        s.tid = tid
        s.form = form
        s._available = True
        s.s_derived = False
        s.p_derived = False
        s.guards = set()#tids
        s.parents = parents
        s.childs = set()
        s.eternal = False
        s.operationp = False
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
    def __str__(s):
        return mk_tdecl(s.tid,s.form)
    def available(s):
        return s._available
    def turnOff(s):
        if not s.eternal:
            s._available = False
    def turnOn(s):
        s._available = True
    def checkBangArrow(s)->bool:
        #A !=> B:turnOff A when derive B
        #add M prefix to avoid Uppercase Variable colision
        return len(twelf.query(f'eq ({s.form}) (MX says ( MF !=> MF2)).'))>0
    def checkArrowBang(s)->bool:
        #A =>! B:turnOff B when A is off
        #add M prefix to avoid Uppercase Variable colision
        return len(twelf.query(f'eq ({s.form}) (MX says ( MF =>! MF2)).'))>0
    def checkReset(s)->'Formula or None':
        l = twelf.query(f'eq {s.tid} (reset ANS).')
        if len(l) > 0:
            return l[0]
    def checkRemove(s)->'Formula or None':
        l = twelf.query(f'eq {s.tid} (remove ANS).')
        if len(l) > 0:
            return l[0]
    def checkNot(s)->'(premise,continuous) or None':
        patterns = ['X says (notexist P => ANS)',
                    'X says (notexist P !=> ANS)',
                    'X says (notexist P =>! ANS)']
        patterns = wrapParen(patterns)
        l = twelf.query(f"({s.tid}) in ({' ^ '.join(patterns)}).")
        if len(l)>0:
            C,P,X = l[0].split(';\n',2)
            P = P.lstrip('P = ').strip()
            X = X.lstrip('X = ').strip()
            return (P,f'{X} says ({C})')
    def checkOperation(s):
        ##if operation "X transfer Y" "X says action Y",
        ##turnOff when used
        patterns = ["MX transfer MY",
                    "MX transfer MY at MT"]
        patterns = wrapParen(patterns)
        p_transfer = len(twelf.query(f'{s.tid} in ({" ^ ".join(patterns)}).'))>0
        #print('p_transfer',p_transfer)

        #excpet => =>! !=>, all are operation
        patterns = ["MX says (MF1 => MF2)",
                    "MX says (MF1 !=> MF2)",
                    "MX says (MF1 =>! MF2)"
                    ]
        patterns = wrapParen(patterns)
        p_not_rules = len(twelf.query(f'{s.tid} in ({" ^ ".join(patterns)}).')) == 0
        #print('p_not_rules',p_not_rules)
        
        patterns = ["MX says MF",
                    "MX says MF at MT"]
        patterns = wrapParen(patterns)
        p_says =  len(twelf.query(f'{s.tid} in ({" ^ ".join(patterns)}).')) > 0
        #print('p_says',p_says)
        return (p_says and p_not_rules) or p_transfer
    def checkTransfer(s)->'prin,s or None':
        patterns = ["X transfer (Y , ANS)"]
        patterns = wrapParen(patterns)
        l = twelf.query(f"({s.tid}) in ({' ^ '.join(patterns)}).")
        if len(l)>0:
            S,Y,X = l[0].split(';\n',2)
            Y = Y.lstrip('Y = ').strip()
            X = X.lstrip('X = ').strip()
            return (Y,S)
    def controls(s,prin:str):
        return len(twelf.query(f'eq {s.tid} (user X controls (action ({prin}))).'))>0
    def match(s,f):
        return len(twelf.query(f'eq {s.tid} ({f}).'))>0
    @staticmethod
    def checkRedundantAnd(form):
        return len(twelf.query(f'eq ({form}) (MX says (MF1 and MF2)).'))>0
    @staticmethod
    def checkFormOperation(form):
        dec = Declaration('tmp',form)
        twelf.decl(str(dec))
        return dec.checkOperation()


class FormSpace:
    def __init__(s):
        s.cnt = 1
        s.D = dict()#the order must be consist during the whole process
        #A dict map tid to twelf declaration
        s.dependency =dict()
        s.set_comb = set()
        s.set_declstrs = set()
        s.set_tids = set()
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
    def add(s,ln:str,dependency=set(),eternal=False,operationp=False):
        tid = mk_tid(s.cnt)
        s.D[tid] = Declaration(tid,ln,set(dependency))
        for p_tid in dependency:
            s.D[p_tid].childs.add(tid)
        s.D[tid].eternal = eternal
        s.D[tid].operationp = operationp
        s.cnt += 1
        return tid
    def turnOff(s,decl):
        decl.turnOff()
        for guard in decl.guards:
            #print(red(f'GUARD together remove {guard}'))
            s.D[guard].turnOff()
    def avail_tids(s):
        return [decl.tid for decl in s.D.values() if decl.available()]
    def avail_declstrs(s):
        return [str(decl) for decl in s.D.values() if decl.available()]
    def avail_decls(s):
        return [decl for decl in s.D.values() if decl.available()]
    def containsAlive(s,form):
        for decl in s.D.values():
            if decl.available():
                if form.strip() == decl.form:
                    return True
        return False
    def checkInTime(s,decl,time_)->'false or form':
        #call twelf to solve the time constraint for use
        patterns = ["(X says (F until ANS))",
                    "(X says (F until ANS => F2))",
                    "(X says (F until ANS =>! F2))",
                    "(X says (F until ANS !=> F2))"]
        r = twelf.query(f"{decl.tid} in ({' ^ '.join(patterns)}).",lambda f:[f.split(';\n')[0]])
        if len(r)>0:
            t = int(r[0])
            #print(red(f't:{t}'))
            if t < time_:
                s.turnOff(decl)
                return False
            else:
                ans = re.sub("until\s+\d+",'',decl.form,1)#replace the first until
                #print('=>',ans)
                return ans
        else:
            return decl.form
    def checkAllInTime(s,time_):
        for decl in s.D.values():
            s.checkInTime(decl,time_)
    def newCombination(s):
        ans = []
        for p_tid in combinations(s.avail_tids(),2):
            if p_tid not in s.set_comb:
                s.set_comb.add(p_tid)
                ans.append(p_tid)
                tid_a,tid_b = p_tid
        return ans
    def useDecl(s,tid)->str:
        decl = str(s.D[tid])
        if decl not in s.set_declstrs:
            s.set_declstrs.add(decl)
        return str(decl)
    def newDeclares(s)->str:#for declaration
        ans = []
        for tid in s.avail_tids():
            decl = str(s.D[tid])
            if decl not in s.set_declstrs:
                s.set_declstrs.add(decl)
                ans.append(str(decl))
        return ans
    def newTids(s):#for single form derivation
        ans = []
        for tid in s.avail_tids():
            if tid not in s.set_tids:
                s.set_tids.add(tid)
                ans.append(tid)
        return ans
    def reach_fixpoint(s):
        #p1 = len(set(s.avail_tids()).difference(s.set_tids)) == 0
        p2 = len(set(s.avail_declstrs()).difference(s.set_declstrs)) == 0
        p3 = len(set(list(combinations(s.avail_tids(),2))).difference(s.set_comb)) == 0
        #return p1 and p2 and p3
        return p2 and p3
    def checkRemove(s,tid):
        if f := s.D[tid].checkRemove():
            #remove
            s.turnOff(s.D[tid])
            for decl in s.D.values():
                if decl.match(f):
                    #print(red(f'REMOVE {decl.tid}'))
                    s.turnOff(decl)
            return True
        return False
    def checkReset(s,tid):
        if f := s.D[tid].checkReset():
            #reset
            s.turnOff(s.D[tid])
            #print(red('RESET'))
            for decl in s.D.values():
                if decl.match(f):
                    s.turnOff(decl)
                    s.revertInfluence(decl)
            return True
        return False
    def checkNot(s,premise):
        for decl in s.D.values():
            if decl.available():
                if decl.match(premise):
                    #print(red(f'{premise} is true in: {str(decl)}'))
                    return False
        return True
    def revertInfluence(s,d):
        #turnOff all his parents
        decls = set([d])
        while decls:
            decl = decls.pop()
            s.turnOff(decl)
            #print(red(f'when reset, turn {decl.tid} off'))
            decls.union(set([s.D[tid] for tid in decl.childs]))

    def show(s,concise=False):
        print("======FormSpace=========")
        for decl in s.D.values():
            if not concise:
                if len(decl.parents) > 0:
                    print(green(f"{' ^ '.join(decl.parents)} -> "),end='')
            print(yellow(decl.tid),end='')
            if not concise:
                if len(decl.childs) > 0:
                    print(green(f" -> {' '.join(decl.childs)} "),end='')
            else:
                print('=', end='')
            if decl.available():
                print(decl.form)
            else:
                print(red(decl.form))

    def graphJson(s):
        nodes = []
        edges = []
        for tid,decl in s.D.items():
            nodes.append({"id":tid,"description":decl.form,"eternal":decl.eternal,
                          "operationp":decl.operationp,
                          "available":decl.available()})
            for child in decl.childs:
                edges.append({"source":tid,"target":child})
        return json.dumps({"nodes":nodes,"edges":edges})

#FS = FormSpace()

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
    def __init__(s,world,mode=3):
        s.UserOpSeq = []#queue
        s.UserOpSeq2 = []#stack
        s.mode = mode
        s.actions = []
        s.transfers = []
        s.cnt = 0
        s._loopcnt = 0
        s.world = world
    def simulateAction(s,l):
        actions = twelf.query(f'find-action ({" ^ ".join(l)}) ANS.')
        actions = dis_duplicate(actions)
        s.actions = actions
    
    def simulateTransfer(s,l):
        l = twelf.query(f'find-transfer ({" ^ ".join(l)}) ANS foo.')
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
            twelf.decl(f"{tid} = {op}.")
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

    def genRandomly(s)->'ln or None':
        if s.mode == 2:
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
        elif s.mode == 3:
            if len(s.UserOpSeq)>0:
                op = s.UserOpSeq.pop()
                s.checkTimes(op)
                return op
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
        #if World.time > 40:
        #    return (lambda x,y,d:f'{x} transfer ({y} , {d} , "B")')(px,py,d)#cheat in Irobot case
        return f(px,py,d)
    def genSaysR(s,px=None,py=None,att=None):
        f = lambda x,a:f"{x} says (action ({a}))"
        if not px:
            px = s.randomPrin("cloud")
        a = s.genActions(py,att)
        if World.time > 65:
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
        N = len(s.UserOpSeq)*2
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

#def tcheckDuplicate(w,target_form)->list:
#    twelf.decl(f"tmp_p = {target_form} .")
#    tids = w.FS.avail_tids()
#    return twelf.query(f'ANS : (tmp_p) in ({tids}).')
def declThenDerive(w,tid,cmd,form):
    def cb(form):
        ans = []
        if form != tid:
            #check if in FS
            if not w.FS.containsAlive(form):#equality check with twelf
                ans.append(form)
        return ans
    twelf.decl(f'{tid} = {form}.')
    return twelf.query(cmd,cb)

def derive(w,forms:"p1 ^ p2"):
    #derive to one solution with twelf derive
    def cb(form):
        a = re.sub('\s+',' ',forms).split(' ')
        b = re.sub('\s+',' ',form).split(' ')
        ans = []
        if b!='' and a != b and a[::-1] != b:
            #check if in FS
            if not w.FS.containsAlive(form):#FALSE,because we should have two reset appeared
                #equality check with twelf
                ans.append(form)
        return ans
    if form1 := list1orEmptyList(twelf.query(f'derive ({forms}) ANS true .',cb)):
        #print('1',form1)
        forms2 = deriveMultiple(w,form1)#if split and success
        ans = []
        if len(forms2) > 0 :
            for form2 in forms2:
                #print('2',form2)
                if form3 := list1orEmptyList(declThenDerive(w,'tmp',f'derive tmp ANS true .',form2)):
                    #print('3',form3)
                    ans.append(form3)
                ans.append(form2)
            return ans
        else:
            return [form1]
    return []

def deriveMultiple(w,form1):
    #derive to multiple solution with twelf deriveMultiple
    #split and
    forms = declThenDerive(w,'tmp',f'deriveMultiple tmp ANS .',form1)
    ans = []
    for form in forms:
        if re.findall('\sand\s',form):#possible to have and
            if Declaration.checkRedundantAnd(form):#abandom redundant and form
                continue
        ans.append(form)
    return ans

def sendAvailableDeclares(w):
    for declstr in w.FS.avail_declstrs():
        twelf.decl(declstr)

def sendAvailableLemmaDeclares(w):
    for decl in w.FS.avail_decls():
        if not decl.eternal:
            twelf.decl(str(decl))

def sendNewDeclares(w):
    for decl in w.FS.newDeclares():
        twelf.decl(decl)
    return True

def ifRemoveImmediatelyUse(w,tid):
    if w.FS.D[tid].form.strip().startswith('remove'):#speed
        #derive reset immediately
        derive(w,tid)
        w.FS.checkRemove(tid)
        return True

def ifResetImmediatelyUse(w,tid):
    if w.FS.D[tid].form.strip().startswith('reset'):#speed
        #derive reset immediately
        derive(w,tid)
        w.FS.checkReset(tid)
        return True

def ifNotPremiseDeriveRest(w,tid):
    if 'notexist' in w.FS.D[tid].form.strip():#speed
        if tup := w.FS.D[tid].checkNot():
            w.FS.turnOff(w.FS.D[tid])#noOwner command flash
            premise,f = tup
            if w.FS.checkNot(premise):
                newtid = w.FS.add(f,[tid])
                decl = w.FS.useDecl(newtid)
                twelf.decl(decl)
                derive(w,newtid)
def ifNoOwnerDeriveRest(w,tid):
    if 'noOwner' in w.FS.D[tid].form.strip():#speed
        if tup := w.FS.D[tid].checkNoOwner():
            w.FS.turnOff(w.FS.D[tid])#noOwner command flash
            prin,f = tup
            if w.FS.checkNoOwner(prin):
                newtid = w.FS.add(f,[tid])
                decl = w.FS.useDecl(newtid)
                twelf.decl(decl)
                derive(w,newtid)
         
def timeMetaRule1(w,form,parents):
    #       [X says F]
    #X says (F        at T)
    #----------------------
    #F at T
    if l:=twelf.query(f'eq ({form}) (X says (F at (time ANS))).'):
        T,F,X = l[0].split(';\n',2)
        F = F.lstrip('F =').strip()
        X = X.lstrip('X =').strip()
        #print(T,F,X,'when check:',form)
        for newform in derive(f'{X} says ({F})'):
            newtid = w.FS.add(newform+ f' at (time {T})',parents)
            tdecl(w.FS.useDecl(newtid))
            ifRemoveImmediatelyUse(w,newtid)
            ifResetImmediatelyUse(w,newtid)
            timeMetaRule1(w,newform,[newtid])
        return True

def instantiateMacro(w,form):
    macroRandom = 'RANDOMS'
    if  macroRandom in form:
        return form.replace(macroRandom, w.seqGen.__next__())
    else:
        return form

def deriveSingleForm(w,tid):
    #print('Derive:',tid)
    w.DS.checkKnows(w.FS.D[tid])
    newforms = derive(w,tid)
    for newform in newforms:
        if Declaration.checkFormOperation(newform):
            newform = instantiateMacro(w,newform)
        newtid = w.FS.add(newform,[tid])
        twelf.decl(w.FS.useDecl(newtid))
        ifNotPremiseDeriveRest(w,newtid)
        ifRemoveImmediatelyUse(w,newtid)
        ifResetImmediatelyUse(w,newtid)
        timeMetaRule1(w,newform,[newtid])

def deriveSingleFormsEternal(w):
    for tid in w.FS.newTids():
        if w.FS.D[tid].eternal:
            deriveSingleForm(w,tid)

def deriveSingleForms(w):
    for tid in w.FS.newTids():
        deriveSingleForm(tid)

def deriveFormPairs(w):
    for tid_pa,tid_pb in w.FS.newCombination():
        w.DS.checkKnows(w.FS.D[tid_pa])
        w.DS.checkKnows(w.FS.D[tid_pb])
        tid_use_lst = []
        for tid in [tid_pa,tid_pb]:
            if f := w.FS.checkInTime(w.FS.D[tid],w.time):
                if f == w.FS.D[tid].form:
                    tid_use_lst.append(tid)
                else:
                    #print(blue(f'delete until,instead use {f}'))
                    twelf.decl(f'{tid}int = {f}.')
                    tid_use_lst.append(f'{tid}int')
            else:
                w.FS.turnOff(w.FS.D[tid])
                print(f'{tid} expired, continue')
                continue

        for newform in derive(w,' ^ '.join(tid_use_lst)):
            if Declaration.checkFormOperation(newform):
                newform = instantiateMacro(w,newform)
            for tid in [tid_pa,tid_pb]:
                if w.FS.D[tid].checkBangArrow():
                    w.FS.turnOff(w.FS.D[tid])
            newtid = w.FS.add(newform,[tid_pa,tid_pb])
            twelf.decl(w.FS.useDecl(newtid))
            
            for tid in [tid_pa,tid_pb]:
                if w.FS.D[tid].checkArrowBang():
                    if tid == tid_pa:
                        w.FS.D[tid_pb].guards.add(newtid)
                        #print(red(f'{newtid} add to {tid_pb} guards'))
                    else:
                        w.FS.D[tid_pa].guards.add(newtid)
                        #print(red(f'{newtid} add to {tid_pa} guards'))

            ifNotPremiseDeriveRest(w,newtid)#debug
            ifRemoveImmediatelyUse(w,newtid)
            ifResetImmediatelyUse(w,newtid)
            timeMetaRule1(w,newform,[newtid])

def tcheckViolations(forms:"p1 ^ p2 ^ ..."):
    #return tquery(f'2ucts ({forms}) ANS .')
    #bad = "userC controls action deviceB"
    bad1 = "bind userC deviceB S"
    bad2 = "bind userA deviceD S"
    ans = []
    if len(twelf.query(f'({bad1}) in ({forms}).'))>0:
        ans.append(f'Attacker Control:{bad1}')
    if len(twelf.query(f'({bad2}) in ({forms}).'))>0:
        ans.append(f'Malicious device added:{bad2}')
    return ans

def tcheckNoSatisfy(forms):
    #good = "userA controls action deviceB"
    good = "bind userA deviceB S"
    if len(twelf.query(f'({good}) in ({forms}).'))==0:
        return [f'User DOS:no {good}']


def checkViolations(w):
    if ps := tcheckViolations(' ^ '.join(w.FS.avail_tids())):
        for p in ps:
            w.PS.add(p)
            return ps
    else:
        return None

def checkNoSatisfy(w):
    if ps := tcheckNoSatisfy(' ^ '.join(w.FS.avail_tids())):
        for p in ps:
            w.PS.add(p)
            return ps
    else:
        return None

def initLogic():
    twelf.read()#eat twelf prompt
    twelf.config()
    twelf.load()

def preprocess(ln):
    #expand $random to random str,etc.
    pass#TODO
    return ln

class Policy():
    def __init__(s):
        s.userDefinedTypes = []
        s.userActionTemplate = []
        s.assumptions = []
    def load(s,w,AE):
        for op in s.userActionTemplate:
            AE.addUserOp(op)
        for form in s.assumptions:
            w.FS.add(form, eternal=True)
        s.loadUserDefineTypes()
    def loadUserDefineTypes(s):
        for declstr in s.userDefinedTypes:
            twelf.decl(declstr+'.')

def readPolicy(path):
    policy = Policy()
    with open(path,'r') as f:
        txt = f.read().strip()
    for blk in txt.split('.'):
        blk = blk.strip()
        if blk == '':continue
        elif blk.startswith('=='):
            return policy
        elif blk.startswith('--'):
            for ln in blk.split('\n'):
                if ln.startswith('=='):
                    return policy
                elif ln.startswith('--'):
                    continue
                else:
                    policy.userActionTemplate.append(ln.strip())
        else:
            if blk.startswith('$'):
                blk = blk.lstrip('$').strip()
                policy.userDefinedTypes.append(blk)
            else:
                policy.assumptions.append(preprocess(blk))
    return policy

def summary(w,AE):
    print("######Summary#########")
    w.FS.show(concise=CONCISE)
    AE.show()
    w.DS.show()
    if len(w.PS)>0:
        for p in w.PS:
            print(blue(p))
    else:
        print("✔️")
    #with open(VISUAL_RST_FILE,'w') as f:#TODO
    #    f.write('const data = '+w.FS.graphJson())

def run(mode=3):
    global policy_path
    if len(sys.argv)>1:
        policy_path = sys.argv[1]
        print('use ',policy_path)

    initLogic()
    w0 = World()
    AE = UserActionEnumerator(w0)
    policy = readPolicy(policy_path)
    policy.load(w0,AE)
    w0.init()
    AE.simulate()
    w = w0
    try:
        while True:
            if op := AE.genRandomly():
                print(op)
                w = w.step(op)
            else:
                break
            if checkViolations(w):
                break
            if STEP:
                #step debug
                FS.show()
                input('Next round?')
    except KeyboardInterrupt:
        print(yellow('stop'))
    checkNoSatisfy(w)
    twelf.quit()
    summary(w,AE)

def test():
    initLogic()
    DS.simulate() 
    tquit()
    summary()

def test2():
    initLogic()
    p1 = 'userA transfer cloud , "deviceB_id"'
    p2 = 'userC says action (deviceB \'s button)'
    p3 = 'foo'
    fs1 = FormSpace()
    ds1 = DecisionSpace()
    ds1.addUserOp(p1)
    tid = fs1.add(p1)
    tid2 = fs1.add(p2,[tid])
    
    fs2 = deepcopy(fs1)
    ds2 = deepcopy(ds1)
    fs1.add(p3,[tid2])
    fs1.turnOff(tid)
    ds1.addUserOp(p2)
    fs1.show()
    fs2.show()
    
    ds1.show()
    ds2.show()
    tquit()

def test3():
    t = Twelf()
    t.read()
    t.config()
    t.load()
    t.interact()
    t.restart()
    t.read()
    t.interact()

if __name__ == '__main__':
    #run()
    test3()
