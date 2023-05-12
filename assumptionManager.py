#!/bin/python3
from itertools import combinations
import re
import json
import time
import re
from helper import *
from copy import deepcopy

class Declaration:
    def __init__(s,twelf,tid,form,parents=set()):
        s.twelf = twelf
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
            if k != 'twelf':
                setattr(result, k, deepcopy(v, memo))
            else:
                setattr(result, k, v)#shallow
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
        return len(s.twelf.query(f'eq ({s.form}) (MX says ( MF !=> MF2)).'))>0
    def checkArrowBang(s)->bool:
        #A =>! B:turnOff B when A is off
        #add M prefix to avoid Uppercase Variable colision
        return len(s.twelf.query(f'eq ({s.form}) (MX says ( MF =>! MF2)).'))>0
    def checkReset(s)->'Formula or None':
        l = s.twelf.query(f'eq {s.tid} (reset ANS).')
        if len(l) > 0:
            return l[0]
    def checkRemove(s)->'Formula or None':
        l = s.twelf.query(f'eq {s.tid} (remove ANS).')
        if len(l) > 0:
            return l[0]
    def checkNot(s)->'(premise,continuous) or None':
        patterns = ['X says (notexist P => ANS)',
                    'X says (notexist P !=> ANS)',
                    'X says (notexist P =>! ANS)']
        patterns = wrapParen(patterns)
        l = s.twelf.query(f"({s.tid}) in ({' ^ '.join(patterns)}).")
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
        p_transfer = len(s.twelf.query(f'{s.tid} in ({" ^ ".join(patterns)}).'))>0
        #print('p_transfer',p_transfer)

        #excpet => =>! !=>, all are operation
        patterns = ["MX says (MF1 => MF2)",
                    "MX says (MF1 !=> MF2)",
                    "MX says (MF1 =>! MF2)"
                    ]
        patterns = wrapParen(patterns)
        p_not_rules = len(s.twelf.query(f'{s.tid} in ({" ^ ".join(patterns)}).')) == 0
        #print('p_not_rules',p_not_rules)
        
        patterns = ["MX says MF",
                    "MX says MF at MT"]
        patterns = wrapParen(patterns)
        p_says =  len(s.twelf.query(f'{s.tid} in ({" ^ ".join(patterns)}).')) > 0
        #print('p_says',p_says)
        return (p_says and p_not_rules) or p_transfer
    def checkTransfer(s)->'prin,s or None':
        patterns = ["X transfer (Y , ANS)"]
        patterns = wrapParen(patterns)
        l = s.twelf.query(f"({s.tid}) in ({' ^ '.join(patterns)}).")
        if len(l)>0:
            S,Y,X = l[0].split(';\n',2)
            Y = Y.lstrip('Y = ').strip()
            X = X.lstrip('X = ').strip()
            return (Y,S)
    def controls(s,prin:str):
        return len(s.twelf.query(f'eq {s.tid} (user X controls (action ({prin}))).'))>0
    def match(s,f):
        return len(s.twelf.query(f'eq {s.tid} ({f}).'))>0
    @staticmethod
    def checkRedundantAnd(twelf,form):
        return len(twelf.query(f'eq ({form}) (MX says (MF1 and MF2)).'))>0
    @staticmethod
    def checkFormOperation(twelf,form):
        dec = Declaration(twelf,'tmp',form)
        twelf.decl(str(dec))
        return dec.checkOperation()



class FormSpace:
    def __init__(s,twelf):
        s.cnt = 1
        s.D = dict()#the order must be consist during the whole process
        #A dict map tid to twelf declaration
        s.dependency =dict()
        s.set_comb = set()
        s.set_declstrs = set()
        s.set_tids = set()
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
                setattr(result, k, v)#shallow
        return result
    def add(s,ln:str,dependency=set(),eternal=False,operationp=False):
        tid = mk_tid(s.cnt)
        s.D[tid] = Declaration(s.twelf,tid,ln,set(dependency))
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
        r = s.twelf.query(f"{decl.tid} in ({' ^ '.join(patterns)}).",lambda f:[f.split(';\n')[0]])
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
