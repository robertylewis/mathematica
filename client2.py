import socket
import sys
import os

def process(s):
    sep = ' '
    clientsocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    clientsocket.connect(('localhost', 10000))
    clientsocket.send(s)
    buf = ''
    while sep not in buf:
        buf += clientsocket.recv(8)
    #print "buf is:", buf
    num = int(buf)
    #print "num = ", num
    buf = clientsocket.recv(num)
    #buf = clientsocket.recv(1000)
    print buf

def read_from_file():
    path = sys.argv[2]
    f = open(path, "r")
    s = f.read()
    f.close()
    os.remove(path)
    return s

if sys.argv[1] == "-f":
    process(read_from_file())
else:
    process(sys.argv[1])

#f = open("/e/Dropbox/lean/mathematica/temp", "w")
#f.write("writing...")
#f.write(sys.argv[1])
#f.close()

