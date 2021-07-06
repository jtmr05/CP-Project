\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "

%---------------------------------------------------------------------------

\title{
       	Cálculo de Programas
\\
       	Trabalho Prático
\\
       	MiEI+LCC --- 2020/21
}

\author{
       	\dium
\\
       	Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 111
\\\hline
a93202 & Francisco Alexandre Pinto Neves
\\
a93166 & João Pedro Rodrigues Carvalho
\\
a93310 & Joaquim Tiago Martins Roque
\end{tabular}
\end{center}

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b)
\end{code}
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a função
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que
|avg_aux = split avg length| em listas não vazias.

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg :: [Double] -> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.)

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
	|id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
		p1 . id = f
	)(
		p2 . id = g
	)|
%
\just\equiv{ identity }
%
        |lcbr(
		p1 = f
	)(
		p2 = g
	)|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Função auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Animação:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes.

\subsection*{Problema 1} \label{pg:P1}
São dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}
Definir:

\begin{code}
outExpAr X = i1 ()
outExpAr (N a) = i2 (i1 (a))
outExpAr (Bin op a b) = i2 (i2 (i1 (op,(a,b))))
outExpAr (Un op a) = i2 (i2 (i2 (op,a))) 
---
recExpAr h = id -|- (id -|- (id >< (h >< h) -|- id >< h))
---
g_eval_exp a = either (const a) nums where
               nums = either numb ops
               ops = either bins uns
               numb b = b 
               bins (Sum, (a,b)) = a+b
               bins (Product, (a,b)) = a*b 
               uns (Negate, a) = a*(-1)
               uns (E, a) = Prelude.exp a 
---
clean X = outExpAr X
clean (N a) = outExpAr (N a)
clean (Bin Sum a b) = outExpAr (Bin Sum a b)
clean (Bin Product (N 0) b) = outExpAr (N 0)
clean (Bin Product a (N 0)) = outExpAr (N 0) 
clean (Bin Product a b) = outExpAr (Bin Product a b)
clean (Un Negate a) = outExpAr (Un Negate a)
clean (Un E (N 0) ) = outExpAr (N 1)
clean (Un E a) = outExpAr (Un E a)

---
gopt a = g_eval_exp a
\end{code}

\begin{code}
sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a)))) -> (ExpAr a, ExpAr a)
sd_gen = either derivx nums where
          nums = either numb ops
          ops = either bins uns
          derivx () = ( X, N 1)
          numb b = (N b, N 0)
          bins (Sum, ((a1,a2), (b1,b2))) = (Bin Sum a1 b1,Bin Sum a2 b2)
          bins (Product, ((a1, a2), (b1,b2))) = (Bin Product a1 b1,Bin Sum (Bin Product a1 b2) (Bin Product a2 b1))
          uns (E, (a,b)) = (Un E a, Bin Product (Un E a) b)
          uns (Negate, (a,b)) = (Un Negate a, Un Negate b)
\end{code}

\begin{code}
ad_gen v = either derivx nums where
          nums = either numb ops
          ops = either bins uns
          derivx () = (v, 1)
          numb b = (b, 0)
          bins (Sum, ((a1, a2),(b1,b2))) = (a1 + b1, a2 + b2)
          bins (Product, ((a1,a2), (b1,b2))) = (a1*b1, (a1*b2) + (a2 * b1))
          uns (E, (a,b)) = (Prelude.exp a, b*(Prelude.exp a))
          uns (Negate, (a, b)) = (a *(-1), b*(-1))
\end{code}

Alínea 1
Resolução
\\
Alinea 1:
\\
Sabemos que por se tratar de um isomorfismo, $|outExpAr . inExpAr = id|$, logo temos:
\begin{eqnarray*}
\start
  |outExpAr . inExpAr =id|
%
\just\equiv{ Def-inExpAr, Reflexão-+, Fusão-+ }
%
  |[outExpAr . (const X), outExpAr . num_ops] = [i1, i2]|
%
\just\equiv{ Eq-+, Def-|num_ops|, Natural-id }
%
        |lcbr(
        outExpAr . (const X) = i1
    )(
        outExpAr . [N, ops] = i2 . id
    )|  
%
\just\equiv{ Reflexão-+, Fusão-+ aplicada 2 vezes }
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |[outExpAr . N, outExpAr . ops] = [i2 . i1, i2 . i2]|
  \end{array}
\right.
%
\just\equiv{ Eq-+, Def-|ops|, Natural-id }
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |outExpAr . [bin, (uncurry Un)] = i2 . i2 . id|
  \end{array}
\right.
%
\just\equiv{Reflexão-+, Fusão-+ aplicada 2 vezes}
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |[outExpAr . bin, outExpAr . (uncurry Un)] = [i2 . i2 . i1, i2 . i2 . i2] |
  \end{array}
\right.
%
\just\equiv{Eq-+}
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) = i1|\\
      |outExpAr . N = i2 . i1|\\
      |outExpAr . bin = i2 . i2 . i1|\\
      |outExpAr . (uncurry Un) = i2 . i2 . i2|
  \end{array}
\right.
%
\just\equiv{ Igualdade Extensional}
%
\left\{
   \begin{array}{lll}
      |outExpAr . (const X) () = i1 ()|\\
      |outExpAr . N a = i2 . i1 a|\\
      |outExpAr . bin (op, (a, b))= i2 . i2 . i1 (op, (a, b))|\\
      |outExpAr . (uncurry Un) (op, a)= i2 . i2 . i2 (op, a)|
  \end{array}
\right.
%
\just\equiv{ Def-const, Def-Comp, Def-|bin|, Def-uncurry}
%
\left\{
   \begin{array}{lll}
      |outExpAr (const X) = i1 ()|\\
      |outExpAr (N a) = i2 (i1 (a))|\\
      |outExpAr (Bin op a b) = i2 (i2 (i1 (op, (a, b))))|\\
      |outExpAr (Un op a) = i2 (i2 (i2 (op, a)))|
  \end{array}
\right.
\end{eqnarray*}
Sabendo que $|recExpAr|$ irá aplicar uma função que recebe como argumento a todos os elementos que resultam de $|outExpAr|$
Assim, a partir de $|baseExpAr|$ e do sseguinte diagrama:
\begin{eqnarray*}
\xymatrix@@C=2cm{
{|ExpAr a|} \ar@@/^2pc/[rr]^-{outExpAr} & {\cong} & {1 + (a + ((BinOp |><| |ExpAr a| ^ 2) + (|UnOp >< ExpAr a|) ))} \ar@@/^2pc/[ll]^-{inExpAr}
}
\end{eqnarray*}
Temos que:
\begin{eqnarray*} 
recExpAr f = |id + id + id >< |f^2 + | id >< f |
\end{eqnarray*}
\\ \\
Alínea 2:
\\
(Nas alíneas seguintes |ExpAr a| será substituido por |ExpAr| apenas por simplificação)
\\Sabendo que a função $|g_eval_exp|$ se trata do gene do catamorfismo $|eval_exp|$ que tem como objetivo calcular o valor de uma $|ExpAr|$ (dado um valor para substituir a incognita), tendo ainda em conta a definição de $|recExpAr|$ temos o diagrama:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr|
           \ar[d]_-{|eval_exp|}
&
    |1 + (Nat0 + ((BinOp >< ExpAr >< ExpAr) + (UnOp >< ExpAr) ))|
           \ar[d]^{|id + (id + (id >< eval_exp >< eval_exp + id >< eval_exp))|}
           \ar[l]_-{|inExpAr|}
\\
     |a|
&
     |1 + (a + ((BinOp >< a >< a) + (UnOp >< a) ))|
           \ar[l]^-{|g_eval_exp|}
}
\end{eqnarray*}
Assim, prevendo as hipoteses existentes, temos que um |BinOp| pode corresponder a uma soma ou a um produto e que um |UnOp| pode corresponder a um |Negate| ou a um |E|, tendo em conta as propriedades do calculo a que correspondem estas expressões teremos que o gene de |eval_exp| será:
\begin{spec}
g_eval_exp a = [ const a, [numb, [bins, uns]]]
\end{spec}
Com |numb|, |bins| e |uns|, que devolvem o valor de um numero b, o resultado de uma operação binária e o resultado de uma operação unária respetivamente.
\\ \\
Alinea 3:
\\
Nesta alínea pede-se que se implemente os genes da função |optimize_eval| que têm como objetivo calcular o valor de uma expressão mas de uma forma mais eficiente.
Sendo |clean| o gene do anamorfismo responsável por limpar os casos em que ocorre um elemento absorvente da operação e |gopt| o gene do catamorfismo responsável por calcular o valor de uma expressão temos os diagramas:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr|
           \ar[d]_-{|ana clean|}
           \ar[r]_-{|clean|}
&
    |1 + (a + ((BinOp >< ExpAr >< ExpAr) + (UnOp >< ExpAr) ))|
           \ar[d]^{|id + (id + (id >< (ana clean) >< (ana clean) + id >< (ana clean)))|}
\\
     |ExpAr|
           \ar[r]^-{|outExpAr|} 
&
     |1 + (a + ((BinOp >< ExpAr >< ExpAr) + (UnOp >< ExpAr) ))| 
}
\end{eqnarray*}
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr|
           \ar[d]_-{|cata gopt|}
&
    |1 + (Nat0 + ((BinOp >< ExpAr >< ExpAr) + (UnOp >< ExpAr) ))|
           \ar[d]^{|id + (id + (id >< cata gopt >< cata gopt + id >< cata gopt))|}
           \ar[l]_-{|inExpAr|}
\\
     |a|
&
     |1 + (a + ((BinOp >< a >< a) + (UnOp >< a) ))|
           \ar[l]^-{|gopt|}
}
\end{eqnarray*}
Assim sendo |clean| poderá ser definida usando |outExpAr|.
Tendo todas estas situações em conta, sabendo que o elemento absorvente da multiplicação é 0 e sabendo ainda que ${|e|^0}$ é sempre igual a 1 a função clean irá abordar estas situações, nas restantes irá aplicar apenas a função |outExpAr|.

Já a |cata gopt| terá uma função semelhante à de |eval_exp|, calcular o valor de uma |ExpAr|, logo podemos definir |gopt| como sendo igual a |g_eval_exp|.
\\ \\
Alínea 4
\\
Nesta alínea pretende-se definir o gene do catamorfismo de |sd| que tem como objetivo calcular a derivada de uma expressão.
Sabemos que, de acordo com as regras das derivadas por vezes vamos precisar da expressão original (isto é, não derivada) para aplicar outras leis de derivação. 
Para isso pretende-se, ao calcular a derivada de uma expressão, possibilitar o acesso à expressão original, usando-se para isso, tal como sugerido pela forma como |sd| é definido no enunciado, um split em que o lado esquerdo corresponde â expressão original e o direito à derivada.
Assim, temos o diagrama:
\begin{eqnarray*}
\xymatrix@@C=1cm{
    |ExpAr|
           \ar[d]_-{|cata sd_gen|}
&
    |1 + (a + ((BinOp >< ExpAr >< ExpAr) + (UnOp >< ExpAr) ))|
           \ar[d]^{|id + (id + (id >< cata sd_gen >< cata sd_gen + id >< cata sd_gen))|}
           \ar[l]_-{|inExpAr|}
\\
     {|ExpAr|^2}
&
     {1 + (a + ((BinOp |><| |(ExpAr)|^2 |><| |(ExpAr)|^2 ) + (UnOp |><| |(ExpAr)|^2) ))}
           \ar[l]^-{|sd_gen|}
}
\end{eqnarray*}
Daqui temos:
\begin{spec}
sd_gen = [ derivx, [numb, [bins, uns]]]
\end{spec}
Assim, tendo em conta as regras de derivação para as diferentes operações chegamos à definição apresentada.
Com |derivx| a calcular a derivada de uma incognita, |numb| a calcular a derivada de um numero |a|, |bins| e |uns| a calcularem a derivada das expressões binárias e unárias associadas ao tipo |ExpAr|.
\\ \\
Alinea 5
\\
Por fim pede-se para determinar o gene do catamorfismo que calcula o valor (numerico) da derivada de uma expressão.
De forma semelhante à alinea anterior é necessário guardar também o valor original da expressão derivada e ao mesmo tempo o valor da derivada.
Assim temos o diagrama:
\begin{eqnarray*}
\xymatrix@@C=1cm{
    |ExpAr|
           \ar[d]_-{|cata ad_gen|}
&
    |1 + (a + ((BinOp >< ExpAr >< ExpAr) + (UnOp >< ExpAr) ))|
           \ar[d]^{|id + (id + (id >< cata ad_gen >< cata ad_gen + id >< cata ad_gen))|}
           \ar[l]_-{|inExpAr|}
\\
     {|a|^2}
&
     {1 + (a + ((BinOp |><| |a|^2 |><| |a|^2 ) + (UnOp |><| |a|^2) ))}
           \ar[l]^-{|ad_gen|}
}
\end{eqnarray*}
Temos ainda:
\begin{spec}
sd_gen = [ derivx, [numb, [bins, uns]]]
\end{spec}
Mais uma vez, tendo em conta as regras de derivação e que $|ad = p2 . cataExpAr ad_gen|$ chegamos à solução apresentada
em que |derivx| calcula o valor da derivada de |()| que representa uma incogmita, |numb| calcula o valor da derivada de um numero |a| e |bins| e |uns| calculam o valor da derivada das expressões binárias e unárias associadas ao tipo |ExpAr| da forma que é apresentado (mantendo sempre o valor da expressão original de forma a estar acessivel).

\subsection*{Problema 2}
Definir
\begin{code}
loop (a, b, c) = (quot (a*b) c, b+4, c+1)
inic = (1, 2, 2)
prj (a, b, c) = a
\end{code}
por forma a que
\begin{code}
cat = prj . (for loop inic)
\end{code}
seja a função pretendida.
\textbf{NB}: usar divisão inteira.
Apresentar de seguida a justificação da solução encontrada. 
\\ \\
Definição do número $n$ de Catalan:
\begin{eqnarray*}
    catal(n) = \frac{(2n)!}{(n+1)! (n!) }
\end{eqnarray*}
Temos de imediato que $catal(0) = 1$. Devemos agora calcular $catal(n)$ como uma recursão, para podermos aplicar a \emph{regra de algibeira} fornecida. Calculemos, então:
\begin{quote}
    $\frac{catal(n+1)}{catal(n)} 
    =
    \frac{\frac{(2(n+1))!}{((n+1)+1)! (n+1)!}} {\frac{(2n)!}{(n+1)! (n!) }}
    =
    \frac{(2n+2)!(n!)}{(n+2)!(2n)!}
    =
    \frac{(2n+2)(2n+1)(2n)!(n!)}{(n+2)(n+1)(n!)(2n)!}
    =
    \frac{2(n+1)(2n+1)}{(n+2)(n+1)}
    = 
    \frac{4n+2}{n+2}$
\end{quote}
Logo
\begin{eqnarray*}
    catal(n+1) = \frac{4n+2}{n+2} catal(n)
\end{eqnarray*}
Temos, então, a função auxiliar $c(n) = \frac{4n+2}{n+2}$. Podemos decompor $c$ em duas funções, $c1$ e $c2$, tais que: $c1(n) = 4n+2$ e $c2(n) = n+2$. Assim decomposta, é muito simples exprimir $c1$ e $c2$ à custa de si mesmas. Daqui, temos $c1(0) = c2(0) = 2$, $c1(n+1) = 4+c1(n)$ e $c2(n+1) = 1+c2(n)$.

\begin{spec}
catal 0 = 1
catal (n+1) = c1(n) catal(n) / c2(n)


c1 0 = 2
c1 (n+1) = 4+c1(n)


c2 0 = 2
c2(n+1) = 1+c2(n)
\end{spec}
Assim, estamos em condições de aplicar a \emph{regra}, onde $inic = (1, \ \ 2, \ \ 2)$ e $loop (catal, \ c1, \ c2) = (quot \ (catal \cdot c1) \ \ c2, \ 4+c1, \ 1+c2)$.

\subsection*{Problema 3}

\begin{code}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine x1 x2 t = cataList h list where
   h = either nil (cons . (ul1d t >< id))
   list = zip x1 x2
   ul1d t p = (uncurry linear1d p) t

deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] _ = []
deCasteljau l t = hyloAlgForm alg coalg l where
   coalg = divide
   alg = either id aux
   aux (a,b) = calcLine a b t
   divide [x] = i1 x
   divide l = i2 (init l, tail l)

hyloAlgForm = hyloLTree
\end{code}

Comecemos por simplificar a função fornecida $calcLine$, de modo a chegar a uma função equivalente mas mais simples, tornando o algoritmo em questão mais explícito.
Temos:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}

Podemos, então, eliminar a função auxiliar $g$ (ajustando nomes de variáveis):

\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(x1h:x1t) = \x2 t -> case x2 of
                  [] -> nil t
                  x2h:x2t -> concat $ (sequenceA [singl . linear1d x1h x2h, calcLine x1t x2t]) t
\end{spec}

Usando a definição de $sequenceA$, esta última linha fica da seguinte forma:
\begin{spec}
                  x2h:x2t -> concat [singl . linear1d x1h x2h t, calcLine x1t x2t t]
\end{spec}

Nesta situação, estamos a concatenar uma lista de um só elemento com uma outra, pelo que temos:
\begin{spec}
                   x2h:x2t -> cons (linear1d x1h x2h t, calcLine x1t x2t t)
\end{spec}

Daqui, observamos que existem duas listas (em que cada uma representa um ponto) a serem consumidas em simultâneo. Isto porque a interpolação linear entre dois pontos só faz sentido para pontos com a mesma dimensão, ou seja, $length \ x1 == length \ x2$.
No catamorfismo de listas, temos uma única lista a ser consumida. Para contornar este problema, podemos usar a função pré-definida do \Haskell \ $zip$, cuja assinatura é:
\begin{spec}
zip :: [a] -> [b] -> [(a, b)]
\end{spec} 

Isto é possível porque as coordenadas correspondentes entre os dois pontos estão em posições iguais da respetiva lista. Portanto, em conformidade com o tipo de saída de $zip$, o catamorfismo em questão é aplicado a uma lista de pares. Como $NPoint$ é uma lista de |Rational|, serão pares de |Rational|.

\begin{eqnarray*}
\xymatrix@@C=3cm@@R=2cm{
    {A^*}
           \ar[d]_-{|cata h|}
           \ar@@/^/[r]^{outList}
&
    |1 + A ><| {A^*}
           \ar@@/^/[l]_{\cong}^{inList}
           \ar[d]^{|id + id >< (cata h)|}
\\
     |B|
&
     |1 + A >< B|
           \ar@@/^/[l]^-{|h|}
}
\end{eqnarray*}

Já vimos que $A$ será instanciando como |Rational >< Rational|, e pelo tipo de saída da função $calcLine$ temos que $B$ é um $NPoint$, ou seja, $|Rational|^*$. Resta-nos calcular o gene $h$.

Para o caso da esquerda, respeitando a função dada, teremos $nil$. No caso da direita, temos o par cabeça e a cauda, já processada pelo algoritmo. Como $calcLine$ devolve um $NPoint$, devemos calcular a interpolação linear da cabeça usando a função $linear1d$ (\emph{uncurried}) e usar $cons$ para a colocar na lista resultado. De notar ainda que $linear1d$ tem um parâmetro de entrada extra e portanto teremos de definir uma função auxiliar. Logo:
\begin{spec}
  h = either nil (cons . (ul1d t >< id)) 
  where ul1d t p = (uncurry linear1d p) t
\end{spec} 

Então:
\begin{eqnarray*}
\xymatrix@@C=3.5cm@@R=2cm{
    {(|Rational >< Rational|)^*}
           \ar[d]_-{|cata (either nil (cons . (ul1d t) >< id)) |}
           \ar@@/^/[r]^{outList}
&
    |1 + (Rational >< Rational) ><| {(|Rational >< Rational|)^*}
           \ar@@/^/[l]_{\cong}^{inList}
           \ar[d]^{|id + id >< cata (either nil (cons . (ul1d t) >< id))|}
\\
     {|Rational|^*}
&
     |1 + (Rational >< Rational) >< | {|Rational|^*}
           \ar@@/^/[l]^-{|either nil (cons . (ul1d t) >< id)|}
}
\end{eqnarray*}

Temos, assim, a definição de $calcLine$ como um catamorfismo de listas.
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine x1 x2 t = cataList h list where
   h = either nil (cons . (ul1d t >< id))
   list = zip x1 x2
   ul1d t p = (uncurry linear1d p) t
\end{spec}

O algoritmo $deCasteljau$ fornecido trata-se de um algoritmo do género \emph{divide and conquer}, em que, para uma lista com um só elemento, o resultado é o elemento solitário da lista; para os restantes casos, ou seja, listas de $N$ elementos, $\forall N>1$, a função é chamada recursivamente para os primeiros $N-1$ e para os últimos $N-1$ elementos. O resultado de cada uma destas chamadas é depois calculado pela função $calcLine$. Nas aulas, foi estudado um algoritmo em tudo muito semelhante a este. Trata-se do \emph{mergeSort}:
\begin{spec}
mSort :: Ord a => [a] -> [a]
mSort [] = []
mSort l = hyloLTree (either singl merge) lsplit l

merge (l,[])                  = l
merge ([],r)                  = r
merge (x:xs,y:ys) 
                  | x < y     = x : merge(xs,y:ys) 
                  | otherwise = y : merge(x:xs,ys)

lsplit [x] = i1 x
lsplit l   = i2 (sep l) where
     sep []    = ([],[])
     sep (h:t) = let (l,r) = sep t in (h:r,l)
\end{spec}

Podemos adaptá-lo para o problema em questão. Desde já, sabemos que o hilomorfismo a ser usado será o hilomorfismo das \LTree. O gene do anamorfismo, como podemos observar, trata da parte \emph{divide} do algoritmo. Como dissemos anteriormente, usamos a chamada recursiva para os primeiros e para os últimos $N-1$ elementos. Vamos então defini-lo:
\begin{spec}
coalg = divide
divide [x] = i1 x
divide l = i2 (init l, tail l)
\end{spec}

Agora, devemos encontrar o gene do catamorfismo. Para o caso em que o anamorfismo injeta à esquerda, temos um elemento solitário. Ora, para esse caso está trivialmente calculado o ponto a retornar (é o próprio ponto), logo usamos a função identidade. Já para o caso da direita, temos um par de pontos, resultantes da chamada recursiva do algoritmo para parte inicial e para a parte final da lista. A função recebe ainda um parâmetro extra, por isso usamos uma função auxiliar:
\begin{spec}
alg = either id aux
aux (a,b) = calcLine a b t
\end{spec}

Assim, temos a solução para listas não vazias. Resta-nos o caso da lista vazia, que, respeitando o algoritmo, é a própria lista vazia:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] _ = []
deCasteljau l t = hyloAlgForm alg coalg l where
   coalg = divide
   alg = either id aux
   aux (a,b) = calcLine a b t
   divide [x] = i1 x
   divide l = i2 (init l, tail l)
\end{spec}

\subsection*{Problema 4}
Solução para listas não vazias:
\begin{code}
avg = p1.avg_aux
\end{code}

\begin{code}
inNL = either singl cons
outNL[a] = i1(a)
outNL(a:x) = i2(a,x)  
cataNL g = g . recList(cataNL g) . outNL
avg_aux = cataNL(either f g)
  where f = split id (const 1)
        g = split av len
        av(a,(b, c)) = (a + c * b) / (c + 1)
        len(a, (b, c)) = c + 1
\end{code}
Solução para árvores de tipo \LTree:
\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either f g
    where f = split id (const 1)
          g = split av len
          av((a, b), (c, d)) = (a * b + c * d) / (b + d)
          len((a, b), (c, d)) = b + d
\end{code}
Resolução:
\\ 
Alínea 1.
\\
A partir dos dados do problema, podemos inferir o seguinte diagrama:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    {T}
           \ar[d]_-{|cata g|}
           \ar@@/^/[r]^{outNL}
&
    {|F| {T}}
           \ar@@/^/[l]_{\cong}^{inNL}
           \ar[d]^{|F (cata g)|}
\\
     {A}
&
     {|F| {A}}
           \ar@@/^/[l]^-{|F| {A}} 
}
\end{eqnarray*}
Como estamos perante listas não vazias, podemos também inferir será que $|inNL = either singl cons|$, pois, os dois únicos casos possíveis
de uma lista deste tipo serão ou termos um elemento da lista, ou termos uma lista completa.\\
Falta-nos, no entanto, inferir $|outNL|$, mas, já sabemos que, por se tratar de um isomorfismo, $|outNL . inNL = id|$, logo
de forma a obtermos $|outNL|$ vamos resolver essa equação:
\begin{eqnarray*}
\start
  |outNL . inNL = id|
%
\just\equiv{ Def-|inNL| }
  |out . [singl, cons] = id|
%
\just\equiv{ Fusão-+ (lei 20) }
  |[out . singl, out . cons] = id|
%
\just\equiv{ Universal-+ (lei 17) with k = id, f = out . singl, g = out . cons}
%
        |lcbr(
    id . i1 = out . singl
  )(
    id . i2 = out . cons      
  )|
%
\just\equiv{ Natural-id (lei 1) aplicada 2 vezes }
        |lcbr(
    i1 = out . singl      
  )(
    i2 = out . cons      
  )|
%
\just\equiv{ Igualdade Extensional (lei 71) }
        |lcbr(
    (out . singl) x = i1 x   
  )(
    (out . cons) x = i2 x   
  )|
%
\just\equiv{ Def-Comp (lei 72) aplicada 2 vezes }
        |lcbr(
     out(singl x) = i1 x     
    )(
     out(cons (h, t)) = i2 (h, t)     
    )|
%
\just\equiv{ Def-singl, Def-cons }
        |lcbr(
     out[x] = i1 x   
        )(
     out(h:t) = i2 (h, t)     
        )|
\end{eqnarray*}
Tendo já definido $|inNL|$ e $|outNL|$, vamos agora procurar conhecer o catamorfismo.\\
Sabemos de antemão que o comprimento da lista será um natural positivo ou zero e que a média
é um racional/double. Então podemos construir o seguinte diagrama:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    {L}
           \ar[d]_-{|cata g|}
           \ar@@/^/[r]^{outNL}
&
    {|A + A >< L|}
           \ar@@/^/[l]_{\cong}^{inNL}
           \ar[d]^{|id + id >< (cata g)|}
\\
     {|(Rational, Nat0)|}
&
     {|A + A >< (Rational, Nat0)|}
           \ar@@/^/[l]^-{g} 
}
\end{eqnarray*}
Podemos então observar que $|(cata g) = g . (id + id >< (cata g)) . out|$ e que o functor deste
tipo de listas é dado por $|F f = id + id >< f|$.\\
Assim sendo, podemos ver que $|(cata g) = g . F (cata g) . out|$, o que, escrito em Haskell é dado
por $|cataNL = g . recList(cataNL g) . out|$.\\
Temos então tudo o necessário para implementar a primeira alínea sendo que $av$ faz o cálculo da média ponderada
até ao nodo atual, $len$ atualiza o comprimento da lista lido recursivamente, $a$ representa o valor
do nodo da lista atual, $b$ a média calculada recursivamente e $c$ o comprimento da lista já lido.
\\ \\
Alínea 2.
\\
Tendo em conta que o catamorfismo já se encontra definido, não é necessário calculá-lo a ele, nem ao isomorfismo 
$in$/$out$, nem o functor. Logo, resta-nos apenas seguir a linha do pensamento anterior, para esta nova estrutura de dados.\\
Tal como na alínea anterior, $av$ faz o cálculo da média ponderada até ao momento e $len$ atualiza o número de valores lidos.
A diferença surge apenas nas variáveis. Visto que estamos perante uma árvore, teremos de analisar dois lados ao invés de apenas um,
então, como seria de esperar teremos duas variáveis que representam as médias ponderadas até ao nodo atual, $a$ e $c$, e outras duas que
representam os tamanhos lidos recursivamente, $b$ e $d$.\\
\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\begin{verbatim}
// (c) MP-I (1998/9-2006/7) and CP (2005/6-2016/7)

module BTree

open Cp

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x

let outBTree x =
    match x with
    | Empty -> i1 ()
    | Node (a,(l,r)) -> i2 (a,(l,r))

// (2) Ana + cata + hylo -------------------------------------------------------

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree g = baseBTree id g

let rec cataBTree g x = (g << (recBTree (cataBTree g)) << outBTree) x 

let rec anaBTree g x = (inBTree << (recBTree (anaBTree g)) << g) x

let hyloBTree c a x = ((cataBTree c) << (anaBTree a)) x

// (3) Map ---------------------------------------------------------------------

let fmap f t = cataBTree (inBTree << baseBTree f id) t

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree t = cataBTree (inBTree << (id -|- (id >< swap))) t

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------
let singl x = [x]

let inord t =
    let join(x,(l,r)) = l @ (singl x) @ r
    in (either nil join) t

let inordt t = cataBTree inord t

let preord t =
    let f(x,(l,r)) = x :: l @ r
    in (either nil f) t

let preordt t = cataBTree preord t

let postord t =
    let f(x,(l,r)) = l @ r @ (singl x)
    in (either nil f) t

let postordt t = cataBTree postord t

// (4.4) Quicksort -------------------------------------------------------------

let app a l = a :: l

let rec part h t = //pivot / list
    match t with
    | [] -> ([],[])
    | x::xs -> if x < h then ((app x) >< id) (part h xs)
                        else (id >< (app x)) (part h xs)

let qsep list =
    match list with
    | [] -> i1 ()
    | h::t -> let (s,l) = part h t
              in i2 (h,(s,l))

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------

let rec union l1 l2 = 
    match l2 with
    | [] -> l1
    | h::t -> if List.exists (fun e -> e = h) l1 then union l1 t else union (l1 @ [h]) t

let tunion (a,(l,r)) = union (List.map (app a) l) (List.map (app a) r)

let traces x = (cataBTree (either (konst [[]]) tunion)) x

// (4.6) Towers of Hanoi -------------------------------------------------------

let strategy l =
    match l with
    | (d,0) -> i1 ()
    | (d,n) -> i2 ((n-1,d),((not d,n-1),(not d, n-1)))

let hanoi x = hyloBTree inord strategy x

// (5) Depth and balancing (using mutual recursion) --------------------------

let baldepth x = 
    let h (a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1, 1 + (max d1 d2))
    let f ((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))
    let g g1 = either (konst (true, 1)) (h << (id >< f)) g1
    in (cataBTree g) x

let balBTree x = (p1 << baldepth) x

let depthBTree x = (p2 << baldepth) x

// (6) Going polytipic -------------------------------------------------------

let tnat f x =
    let theta (a,b) = a @ b
    in  (either (konst []) (theta << (f >< theta))) x

let monBTree f a = cataBTree (tnat f) a

// alternative to (4.3) serialization ----------------------------------------

let preordt' t = monBTree singl t

// (7) Zipper ----------------------------------------------------------------

type Deriv<'a> = 
    | Dr of bool * ('a  * BTree<'a>)

type Zipper<'a> = List<Deriv<'a>>

let rec plug l t =
    match l with
    | [] -> t
    | (Dr (false,(a,l))::z)  -> Node (a,(plug z t,l))
    | (Dr (true,(a, r))::z)  -> Node (a,(r,plug z t)) 
\end{verbatim}

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
