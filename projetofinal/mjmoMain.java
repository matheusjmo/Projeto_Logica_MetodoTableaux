package tableaux;

import java.util.ArrayList;
import java.util.Scanner;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;

public class mjmoMain {
	
	public static void main(String[] args) {
		FileInputStream input = null;
		try {
			input = new FileInputStream("./inout/Entrada.in");
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
		FileOutputStream output = null;
		try {
			output = new FileOutputStream("./inout/Saida.out");
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
		
		int n = 0, i, j, k, a;
	    String linha, expression, ep;
	    String leftExpr, rightExpr, neg;
	    Node arvore = new Node("", false);
	    ArrayList<Node> appliableNodes = new ArrayList<Node>(), leafs = new ArrayList<Node>();
	    boolean truthValue;
	    char operator;
	    Verificacao verif = Verificacao.NULL;
	    Scanner scan = new Scanner(input);
	    i = n = scan.nextInt();

	    scan.nextLine();
	    

	    while(i > 0) {
	        linha = scan.nextLine();
	        verif = Tipo(linha); // lê o problema
	   
	        
	        if(verif == Verificacao.Satisfativel || verif == Verificacao.Insatisfativel) {
	            expression = actualExpression(linha);         // pega a expressao
	            Node node = new Node(expression, true);
	            arvore = node;
	            
	        }
	        else if(verif == Verificacao.Refutavel || verif == Verificacao.Tautologia) {
	            expression = actualExpression(linha);
	            Node node = new Node(expression, false);
	            arvore = node;
	            
	        }
	        else if(verif == Verificacao.ConsequenciaLogica) {
	            String expressionSet = "";
	            expression = actualExpression(linha);
	            ep = expression;
	            Node node = new Node(expression, false);
	            arvore = node;
	            

	            j = linha.indexOf('{') + 1;

	            int j2 = linha.indexOf('}');
	            if (j2 < 0) expressionSet += linha.substring(j); // pega a substring {A}
	            else expressionSet += linha.substring(j, j2);
	            
	            ArrayList<Node> newNodes;
	            
	            while(expressionSet.length() > 0 && !arvore.isClosed()) {
	                expression = actualExpression(expressionSet);
	                newNodes = arvore.insertFront(expression, true);  // n bifurca
	                if (expressionSet.indexOf(',') == -1)
	                	expressionSet = "";
	                else
	                	expressionSet = expressionSet.substring(expressionSet.indexOf(',')+2, expressionSet.length());

	                if(newNodes.get(0).checkContradiction()) {
	                    newNodes.get(0).markContradiction();
	                }
	                
	                newNodes.clear();
	            }
	        }


	        while(!arvore.isClosed() && !arvore.getAppliableNodes().isEmpty()) {
	            appliableNodes.clear();
	            leafs.clear();
	            
	            // Nós que bifurcam são aplicados por último
	            appliableNodes = singleOpNodeSort(arvore.getAppliableNodes());

	            for(k=0; k < appliableNodes.size(); k++) {

	                expression = appliableNodes.get(k).getExpression();
	                truthValue = appliableNodes.get(k).getTruthValue();
	                operator = logicOperator(expression);

	                if(operator == '~') {
	                    leftExpr = notExpression(expression);
	                    leafs = appliableNodes.get(k).insertFront(leftExpr, !truthValue);
	                }
	                else if(operator == 'v') {
	                	String[] subs = getSubExpression(expression);
	                    leftExpr = subs[0];
	                    rightExpr = subs[1];
	                    
	                    // A v B is false
	                    if(!truthValue) {
	                    	leafs = appliableNodes.get(k).insertFront(leftExpr, truthValue); //// truthValue mudei o valor
	                    	leafs.addAll(appliableNodes.get(k).insertFront(rightExpr, truthValue));
	                    }
	                    // A v B is true
	                    else leafs = appliableNodes.get(k).insertSides(leftExpr, truthValue, rightExpr, truthValue);
	                }
	                else if(operator == '&') {
	                    String[] subs = getSubExpression(expression);
	                    leftExpr = subs[0];
	                    rightExpr = subs[1];

	                    // A & B is true
	                    if(truthValue) {
	                    	leafs = appliableNodes.get(k).insertFront(leftExpr, truthValue); ///// mudei o !truthValue
	                    	leafs.addAll(appliableNodes.get(k).insertFront(rightExpr, truthValue));
	                    }
	                    // A & B is false
	                    else leafs = appliableNodes.get(k).insertSides(leftExpr, truthValue, rightExpr, truthValue);
	                }
	                else if(operator == '>') {
	                	String[] subs = getSubExpression(expression);
	                    leftExpr=subs[0];
	                    rightExpr=subs[1];

	                    // A > B is false
	                    if(!truthValue) {
	                    	leafs = appliableNodes.get(k).insertFront(leftExpr, !truthValue);
	                    	leafs.addAll(appliableNodes.get(k).insertFront(rightExpr, truthValue));
	                    }
	                    // A > B is true
	                    else leafs = appliableNodes.get(k).insertSides(leftExpr, !truthValue, rightExpr, truthValue);
	                }
	                for(a=0; a < leafs.size(); a++) {
	                    if(leafs.get(a).checkContradiction()){
	                        leafs.get(a).markContradiction();
	                    }    
	                }
	                appliableNodes.get(k).markApplied();
	            }
	        }
	        
	        appliableNodes.clear();
	        leafs.clear();
	        
	        String outString = "Problema #" + (n-i+1) + "\n";
	        //System.out.println(outString);
	        

	        if(verif == Verificacao.Satisfativel) {
	            if(arvore.isClosed()) outString += "Nao, nao e satisfativel.\n";
	            else outString += "Sim, e satisfativel.\n";
	        }
	        else if(verif == Verificacao.Insatisfativel) {
	        	if(arvore.isClosed()) outString += "Sim, e insatisfativel.\n";
	        	else outString += "Nao, nao e insatisfativel.\n";
	        }
	        else if(verif == Verificacao.Refutavel) {
	            if(arvore.isClosed()) outString += "Nao, nao e refutavel.\n";
	            else outString += "Sim, e refutavel.\n";
	        }
	        else if(verif == Verificacao.Tautologia) {
	            if(arvore.isClosed()) outString += "Sim, e tautologia.\n";
	            else outString += "Nao, nao e tautologia.\n";
	        }
	        else if (verif == Verificacao.ConsequenciaLogica){
	            if(arvore.isClosed()) outString += "Sim, e consequencia logica.\n";
	            else outString += "Nao, nao e consequencia logica.\n";
	        }

	        i--;
	        if(i > 0) outString += "\n";
	        
	        try {
				output.write(outString.getBytes());
			} catch (IOException e) {
				e.printStackTrace();
			}
	    }
		try {
			output.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	    try {
			input.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    //System.out.println("this is the end");
		
	}
	
	public enum Verificacao {
	    Tautologia, Refutavel, Satisfativel, Insatisfativel, ConsequenciaLogica, NULL;
	}
	
	public static Verificacao Tipo (String linha){
	    if(linha.contains("tautologia")) return Verificacao.Tautologia;
	    else if(linha.contains("refutavel")) return Verificacao.Refutavel;
	    else if (linha.contains("insatisfativel")) return Verificacao.Insatisfativel;
	    else if (linha.contains("satisfativel")) return Verificacao.Satisfativel;
	    else if (linha.contains("consequencia logica")) return Verificacao.ConsequenciaLogica;
	    else return Verificacao.NULL;
	}
	
	public static char logicOperator (String expression){
	    int i=1, op=0, cp=0;
	    char operator;
	    
	    if (expression.charAt(i) == '~') operator = '~';
	    else {
	        while(i < expression.length()) {
	        	switch (expression.charAt(i)) {
		        	case '(':
		        		op++;
		        		break;
		        	case ')':
		        		cp++;
		        		break;
	        	}
	            i++;
	            if(cp == op) break;
	        }
	        operator = expression.charAt(i+1);  // pega qnd os parenteses fecham
	    }
	    return operator;
	}
	
	public static String notExpression(String expression) {
		int i=2, op=0, cp=0;
		String negatedExpression = "";
		
		if(expression.charAt(i)=='(' && i< expression.length()) {
			op++;
			negatedExpression += expression.charAt(i);
			i++;
			while(i < expression.length() && op > cp) {
				switch (expression.charAt(i)) {
		        	case '(':
		        		op++;
		        		break;
		        	case ')':
		        		cp++;
		        		break;
				}
	            negatedExpression += expression.charAt(i);
	            i++;
	        }
		}
	    else {
	    	int j = expression.indexOf(')', i);
	    	if (j < 0) negatedExpression += expression.substring(i);
	    	else negatedExpression += expression.substring(i, j);
	    }
		//System.out.println("not: " + expression);
		//System.out.println(negatedExpression);
	    return negatedExpression;
	}
	
	public static String actualExpression(String line) {
		 	int op = 0, cp = 0, i = 0;
		    String expression = "";

		    // verifica se e expressao atomica
		    if(line.charAt(i) >= 'A' && line.charAt(i) <= 'Z') {
		        expression += line.charAt(i);
		        return expression;
		    }
		    else {
		    	i = line.indexOf('(');
//		    	if (i < 0)
//		    		return expression;
		    	expression += line.charAt(i++);
		    	op++;                                     // contador de parenteses
		        while(i < line.length() && op > cp) {     //op parent esquerda ---- cp parent a direita
		        	switch (line.charAt(i)) {
			        	case '(':
			        		op++;
			        		break;
			        	case ')':
			        		cp++;
			        		break;
		        	}
		            expression += line.charAt(i);
		            i++;
		        }
		    }
		    return expression;
	}
	
	public static String[] getSubExpression(String expression) {
	    int i = 1, op = 0, cp = 0;
	    String leftExpression = "", rightExpression = "";

	    // Expressão entre variaveis (A op B)
	    if(expression.charAt(i) >= 'A' && expression.charAt(i) <= 'Z') {
	        leftExpression += expression.charAt(i);
	        i+=4;
	    }
	    // Expressão de sub-expressões (expr op expr)  
	    else {
	        op++;
	        leftExpression += expression.charAt(i);
	        i++;
	        while(i < expression.length() && op > cp) {
	        	switch (expression.charAt(i)) {
		        	case '(':
		        		op++;
		        		break;
		        	case ')':
		        		cp++;
		        		break;
				}
	            leftExpression += expression.charAt(i);
	            i++;
	        }
	        i+=3;
	    }

	    rightExpression = expression.substring(i, expression.length()-1);
	    String[] array = {leftExpression, rightExpression};
	    return array;
	}
	
	public static ArrayList<Node> singleOpNodeSort(ArrayList<Node> nodes) {
	    ArrayList<Node> appliables = new ArrayList<Node>();
	    int i;
	    char operator;
	    boolean truthValue;
	    for(i = 0; i < nodes.size(); i++) {
	        operator = logicOperator(nodes.get(i).getExpression());
	        truthValue = nodes.get(i).getTruthValue();

	        if((operator == '&' && truthValue == true) || 
	           (operator == 'v' && truthValue == false) || 
	           (operator == '>' && truthValue == false) || 
	           (operator == '~')){
	            appliables.add(0, nodes.get(i)); //bota q n bifurcam no inicio
	        }
	        else appliables.add(nodes.get(i));
	    }
	    return appliables;
	}

}
