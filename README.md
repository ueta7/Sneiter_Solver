# Sneiter_Solver
This is an exact solver for Steiner tree problem.
This code is based on wata-orz' codes(https://github.com/wata-orz/steiner_tree).
Original codes is made for  the Parameterized Algorithms and Computational Experiments Challenge 2018 (https://pacechallenge.wordpress.com/pace-2018/).
This challenge includes three tracks, but this code is only suitable for track1.
Original codes are written in RUST, So I write this in C++.
Please refer to the original website for details on the algorithm.

このコードは最小シュタイナー木の厳密解を高速に解くアルゴリズムです。
これは、wata-orz氏のコード
（https://github.com/wata-orz/steiner_tree
）に基づいています。
元のコードは、Parameterized Algorithms and Computational Experiments Challenge 2018（
https://pacechallenge.wordpress.com/pace-2018/
）のために作成されました。
このチャレンジには3つのトラックがありますが、このコードはトラック1にのみ適しています。
元のコードはRUSTで書かれていましたので、私はこれをC++で書き直しました。
アルゴリズムの詳細については、元のウェブサイトを参照してください。

## Required
- g++
## How to build
~~~
$ g++ -o ./out ./main.cpp -O2
~~~

## input
入力は以下の形に合わせてください。
~~~
/*
vector<vector<pair<int,int>>> g
g[u]={{v0,w0},{v1,w1},...}
road from u to vi which weight is wi.

vector<int> ts
terminals (Points are needed.)

vector<pair<int,int>> ans
Road from point.A to point.B
*/
vector<pair<int,int>> ans = Sneiter_Solver::solve(g, ts,1);
~~~
