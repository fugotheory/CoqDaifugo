# CoqDaifugo
wonderful theory of Daifugo games

大富豪ゲームに関する理論を定理証明支援系Coqで証明しています。

Theorems about Daifugo games were proven with Coq, a reliable proof asistant.

## 二人単貧民の基本定理 The main theorem of Tanhinmin

単貧民は二人、一枚出し、特殊ルールなしの大富豪です。  
二人単貧民はゲーム木探索を用いずとも以下のように勝敗を計算できます。


- 先手手札　<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;X" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;X" title="X" /></a>

- 後手手札　<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;\bar{X}" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;\bar{X}" title="\bar{X}" /></a>

- 場の強さ　<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;r" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;r" title="r" /></a> （0が空、1以上が場札の強さ）

- 手札 <a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;X" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;X" title="X" /></a> から最も弱い札一枚を除いた手札　<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;X_{-}" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;X_{-}" title="X_{-}" /></a>  
手札 <a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;\bar{X}" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;\bar{X}" title="\bar{X}" /></a> から最も弱い札一枚を除いた手札　<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;\bar{X}_{-}" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;\bar{X}_{-}" title="\bar{X}_{-}" /></a>


- 手札 <a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;Y" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;Y" title="Y" /></a> から手札 <a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;Z" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;Z" title="Z" /></a> へ、それぞれの札からより弱い札へ辺を引いた二部グラフの最大マッチング数を表す関数　<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;\mu(Y,&space;Z)" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;\mu(Y,&space;Z)" title="\mu(Y, Z)" /></a>

として先手必勝の必要十分条件は

<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{300}&space;\mu&space;(X,&space;\bar{X}_{-}&space;&plus;&space;\{r\})&space;>&space;\mu&space;(\bar{X},&space;X_{-})\text{.}" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{300}&space;\mu&space;(X,&space;\bar{X}_{-}&space;&plus;&space;\{r\})&space;>&space;\mu&space;(\bar{X},&space;X_{-})\text{.}" title="\mu (X, \bar{X}_{-} + \{r\}) > \mu (\bar{X}, X_{-})\text{.}" /></a>

### 例

<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;X&space;=&space;\{1,&space;1,&space;3,&space;4\},&space;\bar{X}&space;=&space;\{1,&space;2,&space;3,&space;5\},&space;r&space;=&space;0" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;X&space;=&space;\{1,&space;1,&space;3,&space;4\},&space;\bar{X}&space;=&space;\{1,&space;2,&space;3,&space;5\},&space;r&space;=&space;0" title="X = \{1, 1, 3, 4\}, \bar{X} = \{1, 2, 3, 5\}, r = 0" /></a>

![Solving Tanhinmin](tanhinmin.png)

<a href="https://www.codecogs.com/eqnedit.php?latex=\dpi{150}&space;\mu(X,&space;\bar{X}_{-}&space;&plus;\{r\})&space;=&space;3,&space;\mu(\bar{X},&space;X_{-})&space;=&space;2" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\dpi{150}&space;\mu(X,&space;\bar{X}_{-}&space;&plus;\{r\})&space;=&space;3,&space;\mu(\bar{X},&space;X_{-})&space;=&space;2" title="\mu(X, \bar{X}_{-} +\{r\}) = 3, \mu(\bar{X}, X_{-}) = 2" /></a>

よって **先手必勝**
