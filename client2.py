import socket
import sys

#f = open("temp", "w")
#f.write(sys.argv[1])
#f.close()

sep = ' '

clientsocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
clientsocket.connect(('localhost', 10000))
clientsocket.send(sys.argv[1])
buf = ''
while sep not in buf:
    buf += clientsocket.recv(8)
num = int(buf)
#print "num = ", num
buf = clientsocket.recv(num)
#buf = clientsocket.recv(1000)
print buf
