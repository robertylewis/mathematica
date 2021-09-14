import socket
import sys
import subprocess
import os
import argparse
import time
import threading
DETACHED_PROCESS = 0x00000008


class ServerThread(threading.Thread):
    def run(self):
        #fnull=open(os.devnull,'w')
        #subprocess.Popen(["math", "--noprompt", "-run", '"<<\"~/Dropbox/lean/mathematica/server2.m\""']
                           # ,stdout=fnull, stdin=fnull, stderr=fnull
                            #)
        os.system('wolfram -noprompt -run "<<server2.m" > /dev/null')


def restart_server():
    fnull=open(os.devnull,'w')
    t = ServerThread()
    t.daemon=True
    t.start()
#    return subprocess.Popen(["math", "--noprompt", "-run", '"<<\"~/Dropbox/lean/mathematica/server2.m\""']
#                            ,stdout=fnull#, stdin=fnull, stderr=fnull
#    )

skt = 10000

def process(s, is_global, start_server):
    sep = ' '
    clientsocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        clientsocket.connect(('localhost', skt))
    except socket.error as e:
        time.sleep(.2)
        print("error"), e
        if start_server:
            print("restarting server")
            pid = restart_server()
           # print pid.pid
            time.sleep(.5)
           # print pid.poll()
            clientsocket.connect(('localhost', skt))
        else:
            return
    clientsocket.send((s + ("1" if is_global else "0")).encode('utf-8'))
    buf = ''
    while sep not in buf:
        buf += clientsocket.recv(1).decode('utf-8')
    splt = buf.split(sep, 1)
    num = int(splt[0])
    buf = clientsocket.recv(num).decode('utf-8') #splt[1]
    #while recvd < num:
    #    buf += clientsocket.recv(8)
    #    recvd += 8
    #buf += clientsocket.recv(8)
    print(buf)

def read_from_file(path):
    f = open(path, "r")
    s = f.read()
    f.close()
    os.remove(path)
    return s

parser = argparse.ArgumentParser(description="Communicate with Mathematica.")
parser.add_argument('-f', action='store_true') # file
parser.add_argument('-g', action='store_true') # global
parser.add_argument('-b', action='store_true') # attempt to talk but don't start server
parser.add_argument('-s', action='store_true') # only attempt to start server
parser.add_argument('cmd')
args = parser.parse_args()

if args.s:
    restart_server()
elif args.f:
    process(read_from_file(args.cmd), args.g, not args.b)
else:
    process(args.cmd, args.g, not args.b)

