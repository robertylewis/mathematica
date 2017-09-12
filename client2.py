import socket
import sys
import os
import argparse

def process(s, is_global):
    sep = ' '
    clientsocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    clientsocket.connect(('localhost', 10000))
    clientsocket.send(s + ("1" if is_global else "0"))
    buf = ''
    while sep not in buf:
        buf += clientsocket.recv(8)
    splt = buf.split(sep, 1)
    num = int(splt[0])
    recvd = 8
    buf = splt[1]
    while recvd < num:
        buf += clientsocket.recv(8)
        recvd += 8
    buf += clientsocket.recv(8)
    print buf

def read_from_file(path):
    f = open(path, "r")
    s = f.read()
    f.close()
    os.remove(path)
    return s

parser = argparse.ArgumentParser(description="Communicate with Mathematica.")
parser.add_argument('-f', action='store_true') # file 
parser.add_argument('-g', action='store_true') # global
parser.add_argument('cmd')
args = parser.parse_args()

if args.f:
    process(read_from_file(args.cmd), args.g)
else:
    process(args.cmd, args.g)

