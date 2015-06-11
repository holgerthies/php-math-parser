<?php
/*** A simple parser for mathematical expressions
 ***/
class MathParser{

  private $function_symbols=[];
  private $operator_symbols = [];
  private $left_associativity = array();
  private $right_associativity = array();
  private $precedence = array();
  private $variable_symbol = 'x';
  private $operations=[];
  private $unary_minus_symbol;

  /* constructor defines unary minus symbol */
  public function __construct(){
    $this->unary_minus_symbol = "<!".uniqid()."!>"; // replace by something that is not used yet so that it won't be seen as operator
  }

  /* preprocesses the string so it can be tokenized
   * In particular removes spaces and replaces unary minus (-)
   * by a new symbol to simplify parsing
   */
  private function preprocess($expression){
    $expression = str_replace(' ', '', $expression); // spaces are ignored
    // minus at the beginning is a unary minus
    if($expression[0] == '-') 
      $expression = $this->unary_minus_symbol.substr($expression, 1);
    for($i=1; $i<strlen($expression); $i++){
      // binary minus can only follow closing paranthesis or number
      if($expression[$i] == '-' && $expression[$i-1] != ']' && $expression[$i-1] != ')' && !is_numeric($expression[$i-1]))
        $expression = substr($expression, 0, $i).$this->unary_minus_symbol.substr($expression, $i+1);
    }
    return $expression;
  }
  
  /*
   * test if string is a variable and if yes parse it 
   * variables have the form x[n] 
   * where x is the string in $variable_symbol
   * and n is an integer
   * if the string is a variable return array("var" => n) 
   * otherwise false
   */
  private function parse_variable($str){
    if(strpos($str, $this->variable_symbol) !== 0) return false;
    if($str[strlen($this->variable_symbol)] != '[') return false;
    if(substr($str, -1) != ']') return false;
    $id = substr($str, strlen($this->variable_symbol)+1, -1);
    if(!ctype_digit($id)) return false;
    return array("var" => intVal($id) );
  }

  /*
   * read a string of a mathematical expression and return array of tokens
   */
  private function tokenize($expression){
    if(strlen($expression) == 0) return array(); // empty expression
    // use backtracking to find tokenization of input string that uses only
    // valid function symbols, operators and numbers
    $current_token = $expression[0];
    for($i=1; $i<=strlen($expression); $i++){
      if($i < strlen($expression))
        $next_token=$current_token.$expression[$i];
      $var = $this->parse_variable($current_token); // parse variable
      // read a valid token
      if(is_numeric($current_token) && ($i == strlen($expression) || !is_numeric($next_token))
          || in_array($current_token, $this->function_symbols) 
          || (in_array($current_token, $this->operator_symbols)) 
          || ( $current_token == "(" )
          || ( $current_token == ")" )
          || ( $current_token == ",")
          ||  $var !== false)
      {
        // parse the rest of the string as new expression
        // and check if its valid
        $tokens = $this->tokenize(substr($expression, $i));
        if($tokens !== false){
          if($var !== false)
            array_unshift($tokens, $var);
          else
            array_unshift($tokens, $current_token);
          return $tokens;
        }
      }
     if($current_token == $this->unary_minus_symbol) 
       $current_token = "-".$expression[$i];
     else
      $current_token = $next_token;
    }
    return false;
  }
  /* 
   * transform expresion from infix notation to reverse polish notation 
   */
  private function shunting_yard($tokens){
    $q = [];
    $stack = new \SplStack();
    foreach($tokens as $t){
      if(is_numeric($t) || is_array($t)){ //number or variable
        array_push($q, $t); // push variables to queue
      }
      else if(in_array($t, $this->function_symbols)){
        $stack->push($t); // push function symbols to stack
      }
      else if($t == ","){ // argument seperator for functions
        // look for left paranthesis
        while(!$stack->isEmpty() && $stack->top() != '('){
         $op = $stack->top();
          // pop operators from stack
         array_push($q, $op);
         $stack->pop();
        }
        if($stack->isEmpty()){
          return false; // misplaced seperator or paranthesis
        }
      }
      else if(in_array($t, $this->operator_symbols)){

        // as long as there is an operator on top of the stack
        while(!$stack->isEmpty() && in_array($stack->top(), $this->operator_symbols)){
          $op = $stack->top();
          if($this->left_associativity[$t] && $this->precedence[$t] <= $this->precedence[$op] ||
            $this->right_associativity[$t] && $this->precedence[$t] < $this->precedence[$op])
          {
            // pop from operator stack
            $stack->pop(); 
            array_push($q, $op);
          } 
          else
          {
            break;
          }
        }
        $stack->push($t);
      }
      else if($t == "("){
        $stack->push($t);
      }
      else if($t == ")"){
        // look for left paranthesis
        while(!$stack->isEmpty() && $stack->top() != "("){
          $op = $stack->top();
          // pop operators from stack
          $stack->pop();
          array_push($q, $op);
        }
        if($stack->isEmpty()){
          return false; // misplaced paranthesis
        }
        // pop left paranthesis
        $stack->pop();
        // if token on top is a function symbol pop it onto queue
        if(in_array($stack->top(), $this->function_symbols)){
          array_push($q, $stack->pop());
        }
      }
    }
    while(!$stack->isEmpty()){
      $op = $stack->pop();
      if($op == "(") return false; //misplaced paranthesis
      array_push($q, $op);
    }
    return $q;
  }

  /***
   * evaluates a formula given in reverse polish notation
   * and an associative array of variables 
  ***/
  private function evaluateRPN($tokens, $var){
    $stack = new \SplStack();
    foreach($tokens as $t){
      if(is_numeric($t)){
        $stack->push(floatVal($t));
      }
      else if(is_array($t)){ // variable
        $stack->push($var[$t['var']]);
      } 
      else{ // operator
        $f = new \ReflectionFunction($this->operations[$t]);
        $params = $f->getNumberOfParameters();
        if($stack->count() < $params)
          return false; // not enough values
        $args = [];
        for($i=0; $i<$params;$i++) array_unshift($args, $stack->pop());
        $result = $f->invokeArgs($args);
        $stack->push($result); // push result of computation back to stack
      }
    }
    if($stack->count() == 1) return $stack->pop();
    return false; // too many arguments
  }
  
  /* register a new function symbol with given name and
   * corresponding function
   */
  public function registerFunction($name, $f){
    $this->function_symbols[] = $name;
    $this->operations[$name] = $f; 
  }

  
  /* register a new binary operator symbol with given name and
   * corresponding function
   * $associativity is string "left", "right" or "both"
   * $precedence is a number that gives the operator precedence
   */
  public function registerOperator($name, $f, $precedence=1, $associativity="both"){
    $this->operator_symbols[] = $name;
    $this->operations[$name] = $f; 
    $this->precedence[$name] = $precedence;
    $this->left_associativity[$name] = false;
    $this->right_associativity[$name] = false;
    if($associativity == "left" || $associativity == "both")
      $this->left_associativity[$name] = true;
    if($associativity == "right" || $associativity == "both")
      $this->right_associativity[$name] = true;
  }
  
  /** evaluate a given mathematical expression that uses registered function and operator symbols 
   * variables in the formula have the form x[n] where x is the variable symbol and n is a positive integer
   * variables are replaced by the values given by the associative array $variables */
  public function evaluate($expression, $variables){
    $expression = $this->preprocess($expression);
    $tokens = $this->tokenize($expression);
    $rpn = $this->shunting_yard($tokens);
    return $this->evaluateRPN($rpn, $variables);
  }
  
  /* returns the ids of variables contained in a formula */
  public function getVariableIds($expression){
    $expression = $this->preprocess($expression);
    $tokens = $this->tokenize($expression);
    $variables = [];
    foreach($tokens as $t){
      if(is_array($t) && !in_array($t["var"], $variables)) $variables[] = $t["var"];
    } 
    return $variables;
  }
}
?>
