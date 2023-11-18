# Analyzer Certificator

## Static Analyser which only accept Exec on Constant

```log
On initial programs (ok0.txt to ok14.txt and bad1.txt to bad8.txt):
Accepted: ok0.txt ok1.txt 
Rejected: bad1.txt bad2.txt bad3.txt bad4.txt bad5.txt bad6.txt bad7.txt bad8.txt ok2.txt ok3.txt ok4.txt ok5.txt ok6.txt ok7.txt ok8.txt ok9.txt ok10.txt ok11.txt ok12.txt ok13.txt ok14.txt ok15.txt 
With automatic testing:
Your analyzer has rejected 145076 programs and accepted 0 dangerous programs on a total of 241977 programs

Your analyzer has rejected 60.0% of the programs ...you can do better!
Your analyzer seems to be correct, that's great!

Overall precision of the analyzer is 2 (min=0 and max=6)
```

## Static Analyser big brain full of water

```log
Your static analyzer accepts the following bad programs: List(bad4.txt)
That's VERY bad!
```
