#! /usr/bin/python
import sys, string, os, popen2, shutil, platform, subprocess, pprint, time, mfgraph
import util
from math import sqrt

#benchmark names
benchmarks= ["SHA", "SHA-SSE", "SHA-equiv", "ChaCha", "ChaCha-SSE", "ChaCha-equiv", "AES-enc", "AES-dec", "AES-key-enc", "AES-key-dec"]
#result folder
resFolder = "../result"
#Each Test Subfolders
test1Folder = "Test2"
test2Folder = "Test3"
test3Folder = "Test1"
#benchmark filenames
benchFile = ["sha", "shasse", "shaequiv", "chacha", "chachaequiv", "chachasse", "aesenc", "aesdec", "aeskeyenc", "aeskeydec"]

#naive
hash_table0_results = [float("inf"), float("inf"), float("inf"), float("inf"), float("inf"), float("inf"), float("inf"), float("inf"), float("inf"), float("inf")]
hash_table1_results = []
hash_table2_results = []
hash_table3_results = []

for bf in benchFile :
    # Go to resFolder/test1Folder/bf and check:
    filePath = resFolder + "/" + test1Folder + "/" + bf
    fp = open(filePath, "r")
    line = fp.readline()
    if line.startswith("p1 is equivalent to p2") :
        line2 = fp.readline()
        hash_table1_results.append(float(line2.split(":")[1].strip()))
    elif line.startswith("p1 is not equivalent to p2 (Reason: SMT Timeout)") :
        hash_table1_results.append(float("inf"))        
    fp.close()
    
    # Go to resFolder/test2Folder/bf and check:
    filePath = resFolder + "/" + test2Folder + "/" + bf
    fp = open(filePath, "r")
    line = fp.readline()
    if line.startswith("p1 is equivalent to p2") :
        line2 = fp.readline()
        hash_table2_results.append(float(line2.split(":")[1].strip()))
    elif line.startswith("p1 is not equivalent to p2 (Reason: SMT Timeout)") :
        hash_table2_results.append(float("inf"))        
    fp.close()

    # Go to resFolder/test3Folder/bf and check:
    filePath = resFolder + "/" + test3Folder + "/" + bf
    fp = open(filePath, "r")
    line = fp.readline()
    if line.startswith("p1 is equivalent to p2") :
        line2 = fp.readline()
        hash_table3_results.append(float(line2.split(":")[1].strip()))
    elif line.startswith("p1 is not equivalent to p2 (Reason: SMT Timeout)") :
        hash_table3_results.append(float("inf"))        
    fp.close()


labels = ["Single query", "CASM-Verify without QuickCheck and MemoryOpt", "CASM-Verify without MemoryOpt", "CASM-Verify"]

i=10

total = 0.0
total1 = 0.0
total2 = 0.0

def generate_bar_example():
   stacks=[]
   bars=[]
   tempval = 0.25
   output_list = ""
   for j in range(i):
       bars=[]


       numbers = []
       if(float(hash_table0_results[j]) > 43200):
           output_list = output_list + "graph 2 newstring fontsize 9 x " + str(tempval) + " y 107 hjc vjt rotate 90.0 : " + "inf" + "\n"
           numbers.append(43200)
       else:
           numbers.append(hash_table0_results[j])

       numbers=mfgraph.stack_bars(numbers)
       bars.append([""] + numbers)
       tempval += 1.1
       

       
       numbers = []
       if(float(hash_table1_results[j]) > 43200):
           output_list = output_list + "graph 2 newstring fontsize 9 x " + str(tempval) + " y 107 hjc vjt rotate 90.0 : " + "inf" + "\n"
           numbers.append(43200)
       else:
           numbers.append(hash_table1_results[j])

       numbers=mfgraph.stack_bars(numbers)
       bars.append([""] + numbers)
       tempval += 1.1





       
       numbers = []
       if(float(hash_table2_results[j]) > 43200) :
           output_list = output_list + "graph 2 newstring fontsize 9 x " + str(tempval) + " y 107 hjc vjt rotate 90.0 : " + "inf" + "\n"
           numbers.append(43200)
       else:
           numbers.append(hash_table2_results[j])

       numbers=mfgraph.stack_bars(numbers)
       bars.append([""] + numbers)
       tempval += 1.1



       

       numbers = []
       if(float(hash_table3_results[j]) > 43200):
           output_list = output_list + "graph 2 newstring fontsize 9 x " + str(tempval) + " y 107 hjc vjt rotate 90.0 : " + "inf" + "\n"
           numbers.append(43200)
       else:
           numbers.append(hash_table3_results[j])

       numbers=mfgraph.stack_bars(numbers)
       bars.append([""] + numbers)

       stacks.append([benchmarks[j]]+ bars)
       tempval += 2.15
      
   #print stacks

   return [mfgraph.stacked_bar_graph(stacks,
                                     bar_segment_labels = labels,
                                     title = "   ",
                                     title_y = 140,
                                     title_fontsize = "5",
                                     ylabel = "Total Time (sec)",
                                     #xlabel = "Number of pointer jumps",                                                                                                                                   
                                     colors = ["0.375 0.375 0.375", "0.875 0.875 0.875", "0 0 0", "0.625 0.625 0.625"],
                                     legend_x = "2",
                                     legend_y = "125",
                                     legend_type = "Manual",
                                     legend_type_x=[0, 20, 0, 20],
                                     legend_type_y=[10, 10, 0, 0] ,
                                     clip = 300,
                                     ysize = 1.1,
                                     xsize = 6,
                                     ymax = 43200,
                                     patterns = ["solid"],
                                     stack_name_rotate = 25.0,
                                     stack_name_font_size = "6", #bmarks names                                                                                                                              
                                     label_fontsize = "6", #y-axis name                                                                                                                                     
                                     legend_fontsize = "6", #label names                                                                                                                                    
                                     ylog = 10,
                                     ymin = 10,
                                     yhash_marks = [100, 1000, 10000, 43200],
                                     yhash_names = ["100", "1000", "10000", "43200"],
                                     ) + output_list]

jgraphString = generate_bar_example()
mfgraph.run_jgraph("newpage\n".join(jgraphString), "TimeComparison")
