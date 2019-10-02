class Node

/**
 * Método construtor. Inicia o tableau com um nó cuja expressão 
 * é expression e cujo valor-verdade é truthValue. 
 * 
 * Exemplo: Node tableau = new Node("((~P) v P)", false)
 */  
Node(String expression, boolean truthValue)

/**
 * Insere um nó com expressão expression e valor-verdade truthValue em todas as folhas alcançáveis
 * a partir deste nó, e retorna todos os nós adicionados por essa operação.
 * A outra versão permite inserir dois nós.
 * 
 * Exemplo: ArrayList<Node> insertedNodes = node.InsertFront("(~P)", false)
 */
ArrayList<Node> insertFront(String expression, boolean truthValue)
ArrayList<Node> insertFront(String expression1, boolean truthValue1, String expression2, boolean truthValue2)

/**
 * Bifurca a árvore e insere dois nós em cada ramo, um com expressão expression1 e valor-verdade truthValue1,
 * e outro com expressão expression2 e valor-verdade truthValue2, em todas as folhas alcançáveis
 * a partir deste nó, e retorna todos os nós adicionados por essa operação.
 * 
 * Exemplo: ArrayList<Node> insertedNodes = node.InsertSides("P", false, "Q", true)
 */
ArrayList<Node> insertSides(String expression1, boolean truthValue1, String expression2, boolean truthValue2)

/**
 * Retorna todos os nós alcançáveis a partir deste nó em que se pode aplicar uma regra. 
 * Para retornar todos os nós da árvore em que se pode aplicar uma regra, o nó chamado deve ser a raiz.
 * 
 * Exemplo: ArrayList<Node> appliableNodes = tableau.getAppliableNodes()
 */
ArrayList<Node> getAppliableNodes()

/**
 * Marca o nó como sido aplicado uma regra. Ele não aparecerá mais em chamadas de getAppliableNodes().
 * 
 * Exemplo: node.markApplied()
 */
void markApplied()

/**
 * Checa se a subárvore a partir deste nó está fechada.
 * Para saber se o tableau inteiro está fechado, o nó chamado deve ser a raiz.
 * 
 * Exemplo: boolean isClosed = tableau.isClosed()
 */
boolean isClosed()

/**
 * Checa se o nó contradiz algum outro do mesmo ramo.
 * 
 * Exemplo: boolean isContradictory = node.checkContradiction()
 */
boolean checkContradiction()

/**
 * Marca o nó como contraditório. Seu ramo será fechado e ignorado agora em diante.
 * 
 * Exemplo: node.markContradiction()
 */
void markContradiction()

/**
 * Retorna a proposição do nó.
 * 
 * Exemplo: String expression = node.getExpression()
 */
String getExpression()

/**
 * Retorna o valor-verdade do nó.
 * 
 * Exemplo: boolean truthValue = node.getTruthValue()
 */
boolean getTruthValue()

/**
 * Imprime a árvore a partir do nó atual.
 * Para imprimir toda a árvore, o nó chamado deve ser a raiz.
 * 
 * Exemplo: tableau.printTree()
 */
void printTree()