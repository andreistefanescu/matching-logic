# Echo server program
import socket
import subprocess


TIMEOUT = 0.5                   # SMT querry timeout, in seconds

Z3_cmd_list = ["(declare-sorts (IntSeq))",
        "(declare-funs ((len IntSeq Int)))",
        "(assert (forall (A IntSeq) (>= (len A) 0)))"]

def initZ3():
    cmd = "z3"
    cmd += " -smtc"
    cmd += " -si"
    cmd += " -t:" + str(TIMEOUT)
    Z3 = subprocess.Popen(cmd, shell=True, bufsize=0,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    
    for Z3_cmd in Z3_cmd_list:
        Z3.stdin.writelines([Z3_cmd + "\n"])
        print Z3_cmd + "\n" + Z3.stdout.readline().strip()
    
    return Z3

Z3 = initZ3()

def callZ3(querry):
    Z3.stdin.writelines(["(push)\n",
        querry + "\n",
        "(pop)\n"])
    
    print Z3.stdout.readline().strip()
    print Z3.stdout.readline().strip()
    print Z3.stdout.readline().strip()
    result = Z3.stdout.readline().strip()
    print result
    print Z3.stdout.readline().strip()
    return result

HOST = 'localhost'              # Symbolic name meaning all available interfaces
PORT = 7070                     # Arbitrary non-privileged port
BUFSIZ = 4096                   # Buffer size
MAUDE_EOF = '###EOMTCP###';     # Maude querry string terminator

serversocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
serversocket.bind((HOST, PORT))
serversocket.listen(1)

while True:
    conn, addr = serversocket.accept()
    print "receiving querry from ", addr
    msg = ""
    while True:
        data = conn.recv(BUFSIZ)
        msg += data
        if not data or data.find(MAUDE_EOF) != -1: break
    
    formula = msg[0:data.find(MAUDE_EOF)]
    result = callZ3(formula)
    print "sending result to", addr, " :\t", result
    conn.send(result)
    conn.close()
