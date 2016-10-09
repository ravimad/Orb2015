import sys

with open(sys.argv[1]) as f:
    content1 = f.readlines()

with open(sys.argv[2]) as f:
    content2 = f.readlines()

content1 = [int(i.split(" ")[1][:-1]) for i in content1]
content2 = [int(i.split(" ")[1][:-1]) for i in content2]

percentage = 0
for i in range(len(content1)):
	percentage += content1[i]*100.0/content2[i]
percentage = percentage*1.0/len(content1)

print(percentage)
