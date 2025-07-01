import os 
import stat
import argparse

pos = 190
parser = argparse.ArgumentParser()
parser.add_argument("--LeanEuclid_path", type=str)
args = parser.parse_args()

path = f"{args.LeanEuclid_path}/.lake/packages/REPL/REPL/Main.lean"
text = f"  Lean.loadDynlib \"{args.LeanEuclid_path}/.lake/packages/cvc5/.lake/build/lib/libcvc5-1.so\""

print(f"Switch to r&w privilege for {path}.")
os.chmod(path, stat.S_IRWXU)

print(f"Modifying REPL, fix the bug of shared library.")
fp = open(path, 'r')           
s = fp.read()                   
fp.close()                      
a = s.split('\n')
a.insert(190, text)    
s = '\n'.join(a)             
fp = open(path, 'w')
fp.write(s)
fp.close()