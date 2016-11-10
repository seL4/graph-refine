# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)
#!/usr/bin/env python2
import sys, subprocess, re, os


unbounded = "unbounded"
infeasible = "Integer infeasible."

#this cplex footer ends a .ilp file and does 
cplex_end_command='''
End
'''

cplex_footer2='''
optimize
display solution objective
display solution variables -
quit
'''

cplex_presolve_off='''
set
preprocessing
presolve
n
'''

def rmSol(sol_file):
        '''remove existing solution file if it exists'''
        #stop rm from complaining without using the dangerous -f flag
        p = subprocess.Popen(['test','-e',sol_file])
        p.communicate()
        if p.returncode ==0:
            p = subprocess.Popen(['rm',sol_file])
            p.communicate()


def cplexSolve(ilp_file_name,silent=True,sol_file=None,expect_unbounded=False):
        '''call cplex on the specified ilp file'''
        cplex = 'cplex'
        if sol_file == None:
            #This is where Chronos stores the sol file by default, [:-4] removes the .ilp extension
            sol_file = ilp_file_name[:-4] + ".sol"
        rmSol(sol_file)
        f_ilp = open(ilp_file_name, 'r')
        p = subprocess.Popen(cplex,stdin=f_ilp,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        print 'cplex called'
        out,err = p.communicate()
        if not silent:
            print out
        ret = p.returncode
        print 'cplex terminated'
        if not expect_unbounded and (ret or (infeasible in err or infeasible in out) or (unbounded in err or unbounded in out)):
            print 'ilp solver FAILED \nout : %s \nerr: %s\n'%(out,err)
            print 'note that infeasible/unbounded can mean the other, turn off the presolver to investiage which is the case'
            return False
        return parseSolFile(sol_file, expect_unbounded)

def parseSolFile (sol_file, expect_unbounded):
    objective_regex = r".*Objective\s*=\s*(?P<value>.*)\n"
    f_out = open(sol_file,'r')
    for line in f_out:
        if re.search(unbounded,line) or re.search(infeasible, line):
            if expect_unbounded:
                return unbounded
            assert False and "Infeasible/unbounded ilp !!!"
        match = re.search(objective_regex,line)
        if match:
            f_out.close()
            return match.group ('value')
    assert match, "Failed to regex cplex output"

def stripFooter(ilp_file):
        '''strip the footer off the ilp file'''
        f_ilp = open(ilp_file, 'r')
        print "ilp_file %s" % ilp_file
        stripped_name = ilp_file+'_nofooter'
        stripped = open (stripped_name, 'w')
        for line in f_ilp:
                if re.search(r'^End',line):
                    #we are done
                    break
                stripped.write(line)
        stripped.close()
        f_ilp.close()
        print 'footer stripped, %s generated' % stripped_name
        return stripped_name

def endProblem(f_ilp,sol_file_name):
    f_ilp.write(cplex_end_command)
    f_ilp.write('set logfile %s\n' % sol_file_name)

def solveProblem(f_ilp,presolve_off=False):
    if presolve_off:
        f_ilp.write(cplex_presolve_off)
    f_ilp.write(cplex_footer2)

def varsUnbounded(var_s,rest):
    tmp_name = "./temp_ilp.ilp"
    sol_name = tmp_name + ".sol"
    tmp_f = open(tmp_name,'w')
    tmp_f.write("enter Q\nMaximize\n")
    for (i,var) in enumerate(var_s):
        if i != 0:
            tmp_f.write("+ ")
        tmp_f.write("1 %s"% var)
    for line in rest:
        if "set logfile" in line:
            tmp_f.write("set logfile " + sol_name + "\n")
        else:
            tmp_f.write(line)
    tmp_f.flush()
    ret_val = cplexSolve(tmp_name, silent=True, sol_file= sol_name, expect_unbounded=True)
    #os.remove(tmp_name)
    return ret_val == unbounded

def findUnboundedVar(ilp_f_name):
    lp_f = open(ilp_f_name)
    lines = lp_f.readlines()
    for (i,line) in enumerate(lines):
        if 'Maximize' not in line:
            continue
        i = i+ 1
        break
    while lines[i].strip() == '':
        i = i +1
    print "found maximized term: "
    rest_ilp = lines [i+1:]

    line = lines[i]
    terms = line.split('+')
    var_s = []
    for term in terms:
        x = term.strip()
        x = x.split()
        #discard the coeeficent
        var_s.append(x[-1])
    print "there are %d variables" % len(var_s)
    n = len(var_s)
    while len(var_s) > 1:
        print 'n= %d, 0: %d, %d: \n' % (n,n/2,n/2)
        var_s_1= var_s[0:n/2]
        var_s_2= var_s[n/2:]
        print 'var_s_1 %d var_s_2 %d' % (len(var_s_1),len(var_s_2))
        if varsUnbounded (var_s_1,rest_ilp):
            print "unbounded in bot half"
            var_s = var_s_1
        else:
            if not varsUnbounded(var_s_2,rest_ilp):
                print "what !?"
                print "vars[0]: %s, [-1]: %s" %  (var_s[0],var_s[-1])
                assert False

            print "unbounded in top half"
            var_s = var_s_2
        n = len(var_s)

    print "the unbounded variable is : %s" % str(var_s)
    assert len(var_s) == 1

def printUsage():
    print 'usage: <some ilp file> [OPTION]'
    print 'options: --x: run cplex --f: strip footer'

if __name__ == '__main__':
        if len(sys.argv) != 3:
                printUsage()
                sys.exit(1)
        ilp_f_name = sys.argv[1]
        flag = sys.argv[2]
        if flag == '--x':
                ret = cplex(ilp_f_name)
                print 'result : %f' % ret
        elif flag == '--f':
                stripFooter(ilp_f_name)
        elif flag == '--u':
                print 'finding unbounded variable'
                findUnboundedVar(ilp_f_name)
        else:
                printUsage()
                sys.exit(1)
