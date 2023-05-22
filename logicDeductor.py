#!/bin/python3
import re
from helper import *
from assumptionManager import Declaration
CONCISE = False
VISUAL_RST_FILE = './visualize/data.js'

def declThenDerive(w,tid,cmd,form):
    def cb(form):
        ans = []
        if form != tid:
            #check if in FS
            if not w.FS.containsAlive(form):#equality check with twelf
                ans.append(form)
        return ans
    w.twelf.decl(f'{tid} = {form}.')
    return w.twelf.query(cmd,cb)


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
    def easy_cb(form):
        ans = []
        #check if in FS
        form = form.split(';')[0]
        if not w.FS.containsAlive(form):#equality check with twelf
            ans.append(form)
        return ans
    if form1 := list1orEmptyList(w.twelf.query(f'derive ({forms}) ANS true .',cb)):
        #print('1',form1)
        forms2 = deriveMultiple(w,form1)#if split and success
        ans = []
        if len(forms2) > 0 :
            for form2 in forms2:
                #print('2',form2)
                #if form3 := list1orEmptyList(declThenDerive(w,'tmp',f'derive tmp ANS true .',form2)):
                if form3 := list1orEmptyList(w.twelf.query(f'derive ({form2}) ANS true .',easy_cb)):
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
    def easy_cb(form):
        ans = []
        #check if in FS
        form = form.split(';')[0]
        if not w.FS.containsAlive(form):#equality check with twelf
            ans.append(form)
        return ans
    forms = declThenDerive(w,'tmp',f'deriveMultiple tmp ANS .',form1)
    #forms = w.twelf.query(f'deriveMultiple ({form1}) ANS .', easy_cb)
    ans = []
    for form in forms:
        if re.findall('\sand\s',form):#possible to have and
            if Declaration.checkRedundantAnd(w.twelf,form):#abandom redundant and form
                continue
        ans.append(form)
    return ans

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
                w.twelf.decl(decl)
                derive(w,newtid)
def ifNoOwnerDeriveRest(w,tid):
    if 'noOwner' in w.FS.D[tid].form.strip():#speed
        if tup := w.FS.D[tid].checkNoOwner():
            w.FS.turnOff(w.FS.D[tid])#noOwner command flash
            prin,f = tup
            if w.FS.checkNoOwner(prin):
                newtid = w.FS.add(f,[tid])
                decl = w.FS.useDecl(newtid)
                w.twelf.decl(decl)
                derive(w,newtid)
         
def timeMetaRule1(w,form,parents):
    #       [X says F]
    #X says (F        at T)
    #----------------------
    #F at T
    if l:=w.twelf.query(f'eq ({form}) (X says (F at (time ANS))).'):
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
        if Declaration.checkFormOperation(w.twelf,newform):
            newform = instantiateMacro(w,newform)
        newtid = w.FS.add(newform,[tid])
        w.twelf.decl(w.FS.useDecl(newtid))
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
                    w.twelf.decl(f'{tid}int = {f}.')
                    tid_use_lst.append(f'{tid}int')
            else:
                w.FS.turnOff(w.FS.D[tid])
                print(w.FS.D[tid].form)
                print(f'{tid} expired, continue')
                continue

        for newform in derive(w,' ^ '.join(tid_use_lst)):
            if Declaration.checkFormOperation(w.twelf,newform):
                newform = instantiateMacro(w,newform)
            for tid in [tid_pa,tid_pb]:
                if w.FS.D[tid].checkBangArrow():
                    w.FS.turnOff(w.FS.D[tid])
            newtid = w.FS.add(newform,[tid_pa,tid_pb])
            w.twelf.decl(w.FS.useDecl(newtid))
            
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


def sendAvailableDeclares(w):
    for declstr in w.FS.avail_declstrs():
        w.twelf.decl(declstr)

def sendAvailableLemmaDeclares(w):
    for decl in w.FS.avail_decls():
        if not decl.eternal:
            w.twelf.decl(str(decl))

def sendNewDeclares(w):
    for decl in w.FS.newDeclares():
        w.twelf.decl(decl)
    return True


def checkViolations(w):
    def tcheckViolations(forms:"p1 ^ p2 ^ ..."):
        #return tquery(f'2ucts ({forms}) ANS .')
        #bad = "userC controls action deviceB"
        bad1 = "bind userC deviceB S"
        bad2 = "bind userA deviceD S"
        ans = []
        if len(w.twelf.query(f'({bad1}) in ({forms}).'))>0:
            ans.append(f'Attacker Control:{bad1}')
        if len(w.twelf.query(f'({bad2}) in ({forms}).'))>0:
            ans.append(f'Malicious device added:{bad2}')
        return ans

    if ps := tcheckViolations(' ^ '.join(w.FS.avail_tids())):
        for p in ps:
            w.PS.add(p)
            return ps
    else:
        return None

def checkNoSatisfy(w):
    def tcheckNoSatisfy(forms):
        #good = "userA controls action deviceB"
        good = "bind userA deviceB S"
        if len(w.twelf.query(f'({good}) in ({forms}).'))==0:
            return [f'User DOS:no {good}']


    if ps := tcheckNoSatisfy(' ^ '.join(w.FS.avail_tids())):
        for p in ps:
            w.PS.add(p)
            return ps
    else:
        return None

def initLogic(twelf):
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
    def load(s,twelf,w,AE):
        for op in s.userActionTemplate:
            AE.addUserOp(op)
        for form in s.assumptions:
            w.FS.add(form, eternal=True)
        s.loadUserDefineTypes(twelf)
    def loadUserDefineTypes(s,twelf):
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

def summary(w,AE,visual=False):
    print("######Summary#########")
    w.FS.show(concise=CONCISE)
    AE.show()
    w.DS.show()
    if len(w.PS)>0:
        for p in w.PS:
            print(blue(p))
    else:
        print("✔️")
    if visual:
        with open(VISUAL_RST_FILE,'w') as f:#TODO
            f.write('const data = '+w.FS.graphJson())
