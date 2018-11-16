import csv

with open('iladata.csv', 'r') as csvfile:
    csvreader = csv.reader(csvfile, delimiter=',', quotechar='|')
    for row in csvreader:
        if (row[5] == '1'):
            print(row[3])
        if (row[6] == '1'):
            print(row[4])
        # print(', '.join(row[]));