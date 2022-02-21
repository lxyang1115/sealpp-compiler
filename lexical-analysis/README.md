# lex_analysis
利用flex编写seal++程序词法分析器，能够<br>
1.提取出.sealpp文件中的各种单词(关键词、运算符、常量、函数及变量名、逗号括号等)<br>
2.排除注释<br>
3.正确标定单词行号<br>
4.计算整个.sealpp文件中的行数，字数，字符数。

测试环境：Ubuntu16.04 <br>

有关环境安装： <br>
`sudo apt-get install flex bison` <br>
`sudo apt-get install python3.6`

测试结果<br>
![image](https://github.com/lxyang1115/lex_analysis/blob/master/result2.png "RESULT2")
