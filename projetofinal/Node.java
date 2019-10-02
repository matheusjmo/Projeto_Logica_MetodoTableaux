import java.util.ArrayList;
import java.util.stream.Collectors;

public class Node {
    private String expression;
    private boolean truthValue;

    private Node parent;
    private Node leftChild;
    private Node frontChild;
    private Node rightChild;

    private boolean isAppliable;
    private boolean isContradictory;


    /**
     * Método construtor. Inicia o tableau com um nó cuja expressão é expression e
     * cujo valor-verdade é truthValue.
     * 
     * Exemplo: Node tableau = new Node("((~P) v P)", false)
    */
    public Node(String expression, boolean truthValue) {
        this.expression = expression;
        this.truthValue = truthValue;
        this.isAppliable = expression.toString().matches("\\(.*\\)");
        this.isContradictory = false;
    }

    /**
     * Insere um nó com expressão expression e valor-verdade truthValue em todas as
     * folhas alcançáveis a partir deste nó, e retorna todos os nós adicionados por
     * essa operação.
     * 
     * Exemplo: ArrayList<Node> insertedNodes = node.InsertFront("(~P)", false)
    */
    public ArrayList<Node> insertFront(String expression, boolean truthValue) {
        
        ArrayList<Node> insertedNodes = new ArrayList<Node>();
        ArrayList<Node> reachableLeafs = getReachableLeafs();
            for (Node leaf : reachableLeafs) {
                Node child = new Node(expression, truthValue);
                insertNode(leaf, child);
                insertedNodes.add(child);
            }

        return insertedNodes;
    }

    /**
     * Bifurca a árvore e insere dois nós em cada ramo, um com expressão expression1
     * e valor-verdade truthValue1, e outro com expressão expression2 e
     * valor-verdade truthValue2, em todas as folhas alcançáveis a partir deste nó,
     * e retorna todos os nós adicionados por essa operação.
     * 
     * Exemplo: ArrayList<Node> insertedNodes = node.InsertSides("P", false, "Q",
     * true)
     */
    public ArrayList<Node> insertSides(String expression1, boolean truthValue1, String expression2, boolean truthValue2) {
        ArrayList<Node> insertedNodes = new ArrayList<Node>();

        ArrayList<Node> reachableLeafs = getReachableLeafs();
        for (Node leaf : reachableLeafs) {
            Node leftChild = new Node(expression1, truthValue1);
            Node rightChild = new Node(expression2, truthValue2);
            insertNode(leaf, leftChild, rightChild);
            insertedNodes.add(leftChild);
            insertedNodes.add(rightChild);
        }

        return insertedNodes;
    }

    private void insertNode(Node parent, Node child) {
        parent.frontChild = child;
        child.parent = parent;
    }

    private void insertNode(Node parent, Node leftChild, Node rightChild) {
        parent.leftChild = leftChild;
        parent.rightChild = rightChild;
        leftChild.parent = rightChild.parent = parent;
    }

    private ArrayList<Node> getReachableLeafs() {
        ArrayList<Node> reachableLeafs = new ArrayList<Node>();

        ArrayList<Node> allNodes = traverse(new ArrayList<Node>());
        for (Node node : allNodes) {
            if (node.isLeaf())
                reachableLeafs.add(node);
        }
        return reachableLeafs;
    }

    private boolean isLeaf() {
        return leftChild == null && rightChild == null && frontChild == null && !isContradictory;
    }
    
    /**
     * Retorna todos os nós alcançáveis a partir deste nó em que se pode aplicar uma
     * regra. Para retornar todos os nós da árvore em que se pode aplicar uma regra,
     * o nó chamado deve ser a raiz.
     * 
     * Exemplo: ArrayList<Node> appliableNodes = tableau.getAppliableNodes()
    */
    public ArrayList<Node> getAppliableNodes() {
        ArrayList<Node> appliableNodes = new ArrayList<Node>();
            
        ArrayList<Node> allNodes = traverse(new ArrayList<Node>());
        for(Node node : allNodes) {
            if(node.isAppliable)
                appliableNodes.add(node);
        }
        return appliableNodes;
    }

    private ArrayList<Node> traverse(ArrayList<Node> nodes) {
        nodes.add(this);
        if(frontChild != null) 
            frontChild.traverse(nodes);
        else if(leftChild != null && rightChild != null) {
            leftChild.traverse(nodes);
            rightChild.traverse(nodes);
        }
        return nodes;
    }

    /**
     * Marca o nó como sido aplicado uma regra. Ele não aparecerá mais em chamadas
     * de getAppliableNodes().
     * 
     * Exemplo: node.markApplied()
    */
    public void markApplied() {
        isAppliable = false;
    }

    /**
     * Checa se a subárvore a partir deste nó está fechada. Para saber se o tableau
     * inteiro está fechado, o nó chamado deve ser a raiz.
     * 
     * Exemplo: boolean isClosed = tableau.isClosed()
    */
    public boolean isClosed() {
        return getReachableLeafs().isEmpty();
    }

    /**
     * Checa se o nó contradiz algum outro do mesmo ramo.
     * 
     * Exemplo: boolean isContradictory = node.checkContradiction()
    */
    public boolean checkContradiction() {
        for(Node it = this.parent; it != null; it = it.parent) {
            if((it.expression.equals(this.expression) && it.truthValue != this.truthValue) || it.isContradictory)
                return true;
        }
        return false;
    }

    /**
     * Marca o nó como contraditório. Seu ramo será fechado e ignorado agora em
     * diante.
     * 
     * Exemplo: node.markContradiction()
    */
    public void markContradiction() {
        isContradictory = true;
    }

    /**
     * Imprime a árvore a partir do nó atual. Para imprimir toda a árvore, o nó
     * chamado deve ser a raiz.
     * 
     * Exemplo: tableau.printTree()
     */
    public void printTree() {
        printTree(0);
    }

    private void printTree(int level) {
        for(int i = 0; i < level; i++) {
            System.out.print('\t');
        }

        StringBuilder expression = new StringBuilder("v(").append(this.expression).append(") = ").append(truthValue ? "1" : "0").append(isContradictory ? " X " : "");
        System.out.println(expression);
        if(frontChild != null) {
            frontChild.printTree(level + 1);
        } else if(leftChild != null && rightChild != null) {
            leftChild.printTree(level + 1);
            rightChild.printTree(level + 2);
        }

    }

    /**
     * Retorna a proposição do nó.
     * 
     * Exemplo: String expression = node.getExpression()
    */
    public String getExpression() {
        return expression;
    }

    /**
     * Retorna o valor-verdade do nó.
     * 
     * Exemplo: boolean truthValue = node.getTruthValue()
    */
    public boolean getTruthValue() {
        return truthValue;
    }
    
}