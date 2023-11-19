(* TIPO SIMBOLO: Usado na análise Léxica *)
(*  Referente à cada palavra possível de existir na entrada que é passado como string  *)
type simbolo =
  True
| False
| If
| Then
| Else 
| Endif
| Numero
| Suc
| Pred
| EhZero
| Variavel of string
| Lambda
| Colon (* ":" Fiz a opção pelo nome em inglês *) 
| Dot   (* "."  *)
| End
| Arrow (* "->" *)
| Bool 
| Nat 
| LParen (*Left Parentese*)
| RParen (*Right Parentese*)
| Exclamation (* Não teremos "!" como entrada pelo usuário, mas usaremos esse construtor para já iniciarmos o tratamento de um simbolo inválido *)
;;

(*Função que verifica se temos um digito*)
let eh_digito (dig: char): bool =
  match dig with
  | '0' .. '9' -> true
  | _ -> false
;;

(*Função que verifica se determinada palavra é um número seguindo a gramática do trabalho*)
let eh_numero (num: string) : bool =
  let rec aux (digitos: char list) (inicia_com_zero: bool) (count: int) : bool =
    match digitos with 
    | [] -> true (*Lista chegou até o fim, temos um número valido*)
    | h :: t -> if h = '0' && count = 0 then begin (aux [@tailcall]) t true (count+1) end (*Primeiro digito é zero*)
                else if (eh_digito h) && (not inicia_com_zero) then begin (aux [@tailcall]) t false (count+1) end (*Segue a função*)
                else begin false end
  in 
  aux (List.of_seq (String.to_seq num)) false 0
;;

(*Função que verifica se temos uma LETRA*)
let eh_letra (caractere:char): bool =
  match caractere with
  | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _ -> false
;;

(*Função que verifica se determinada palavra é uma Variável seguindo a gramática do trabalho*)
let eh_variavel (coisa: string) : bool =
  let rec aux (caracteres: char list) (count: int): bool =
    match caracteres with
    | [] -> (*Lista chegou até o fim, temos apenas que tratar das palavras chaves para ser uma variável válida*)
            if coisa <> "true" && coisa <> "false" && coisa <> "if" && coisa <> "then" && coisa <> "else" && coisa <> "endif" && coisa <> "suc"
               && coisa <> "pred" && coisa <> "ehzero" && coisa <> "lambda" && coisa <> "Nat" && coisa <> "Bool" && coisa <> "end" then true else false
    | h :: t -> if count = 0 && (eh_letra h) then begin (aux [@tailcall]) t (count+1) end (*Primeiro caractere precisa ser letra*)
                else if count <> 0 && (eh_letra h || eh_digito h) then begin (aux [@tailcall]) t (count+1) end (*Segue pecorrendo*)
                else begin false end
  in
  aux (List.of_seq (String.to_seq coisa)) 0
;;

(*Uma função que retorna uma lista com os simbolos da entrada*)
let recebe_entrada (entrada: string): string list =
  String.split_on_char ' ' entrada
;;

(*Realizando a análise léxica da entrada - Transforma de String List para Simbolo List*)
let analise_lexica (lista: string list): simbolo list =
  let aux (palavra:string): simbolo =
    match palavra with
    | "true" -> True
    | "false" -> False 
    | "if" -> If
    | "then" -> Then
    | "else" -> Else
    | "endif" -> Endif
    | "end" -> End
    | "suc" -> Suc
    | "pred" -> Pred 
    | "ehzero" -> EhZero
    | "lambda" -> Lambda
    | ":" -> Colon
    | "." -> Dot
    | "->" -> Arrow
    | "Bool" -> Bool 
    | "Nat" -> Nat 
    | "(" -> LParen
    | ")" -> RParen
    | coisa -> if eh_numero coisa then Numero else if eh_variavel coisa then Variavel coisa else Exclamation
  in
  List.map aux lista
;;

(*Agora vamos definir Tipos e Termos, o que será útil para 'transformar' um simbolo em um termo*)

type tipo =
  TBool
| TNat
| TFunc of (tipo * tipo) (*TIPO -> TIPO  Exemplo: (Nat,Bool) seria equivalente à Nat -> Bool*)
| Sem_tipo_determinado (*Caso em que iremos jogar a exceção "-"*)
;;

type var = Var of string;; (*Esse tipo é útil devido a questão do contexto que será introduzido em breve no programa*)

type termo =
  True 
| False 
| If of (termo * termo * termo) (*If then else*)
| Numero
| Suc
| Pred
| EhZero
| Var of var
| Appl of (termo * termo) (* TERMO_TERMO*)
| Lamb of (var * tipo * termo) (*LAMBDA*)

(*Antes de podermos tratar de termos, temos que pensar sobre os tipos, assim como é dito nas dicas do enunciado do trabalho*)
(*Então, primeiramente, iremos implementar uma função que recebe um termo e retorna o tipo desse termo *)
(*Entretanto, antes dessa função de tipagem geral de termos, temos que pensar na tipagem de variáveis que é uma situação "especial" *)
(*Por situção especial, eu quis me referir a questão de contexto!*)
(*A ideia é que ao termos uma variavel como termo, teremos que ir verificar seu contexto para fazermos sua tipagem*)
(*Caso essa variavel seja dentro de um termo lambda, então temos a determinação do tipo p/ esse contexto da variável, justamente nesse momento e então, jogamos a variavel e o seu tipo em uma lista de tuplas para que possamos ter várias variáveis (por isso uma lista) e estarmos sempre relacionando determinada variável com seu determinado tipo (por isso uma tupla).Tudo isso pensando em um mesmo contexto, lógico*)
(*Então vamos lá...*)

let rec tipagem_var (variavel: var) (lista: (var * tipo) list): tipo = 
  match lista with
  | (variable, tipo) :: rest -> (if variavel = variable then (*A variavel em questão já foi tipada para esse contexto anteriormente atraves de um                                                                                                                                                    lambda*) 
                                 begin tipo end (*Retornamos o seu tipo*)
                                 else begin (tipagem_var [@tailcall]) variavel rest end ) (*Caso contrário, chama recursivamente*)
  | [] -> Sem_tipo_determinado (*Pois se chegamos até o final da lista e não tivemos nenhum match na condicional acima, siginifica que temos uma                                                       variável sem tipo para o contexto atual, o que lógico, é um problema*)
;;

(*Função de tipagem geral de termos*)
(*A lista de contexto é importante justamente pela questão da tipagem de variaveis*)
let rec tipagem (termo: termo) (lista_contexto: (var * tipo) list): tipo =
  match termo with
  | True -> TBool
  | False -> TBool
  | If (t1,t2,t3) -> ( let tipo_t1 = tipagem t1 lista_contexto in (*É obrigatório, lógico, que seja do tipo Bool esse termo*)
                      let tipo_t2 = tipagem t2 lista_contexto in (*Verificamos o tipo do termo que é a saída da condicional*)
                      let tipo_t3 = tipagem t3 lista_contexto in (*É importante, mas trivial, que t2 e t3 devem possuir o mesmo tipo*)
                      (*Agora, basta verificarmos se tudo está ok, ou não, com essa tipagem*) 
                      if (tipo_t1 = TBool && tipo_t2 = tipo_t3) then tipo_t3 (*Poderia ser tipo_t2 tambem, tanto faz*) else Sem_tipo_determinado )
                                                                                                                            (*Deu algum problema*)
  | Numero -> TNat
  | Suc -> TFunc (TNat, TNat)
  | Pred -> TFunc (TNat, TNat)
  | EhZero -> TFunc (TNat, TBool)
  | Var v -> tipagem_var v lista_contexto (*Temos que verificar o contexto*)
  | Appl (t1,t2) -> (let tipo_t1 = tipagem t1 lista_contexto in (*Tipagem do primeiro termo*)
                     let tipo_t2 = tipagem t2 lista_contexto in (*Tipagem do segundo termo*)
                     begin match (tipo_t1, tipo_t2) with (*Aplica o passo de computação através da regra de aplicação*)
                        | TFunc (t2, a), b -> if t2 = b then a else Sem_tipo_determinado
                        | _ -> Sem_tipo_determinado
                     end )
  | Lamb (v, tipo, termo) -> (let nova_lista_contexto = ((v, tipo) :: lista_contexto) in  (*Tipando uma variavel v nesse contexto atual*)
                              let novo_tipo = tipagem termo nova_lista_contexto in (*Tipando o termo já com a nova lista de contexto*)
                              TFunc (tipo, novo_tipo) )
;;

(*Função auxiliar usada no converter_para_termos*)
(*A ideia é verificar o tipo que é esoecificado dentro de um lambda*)
let rec tipos (lista: simbolo list): (tipo * simbolo list)= 
  match lista with
  | LParen :: r1 -> ( let (t1,r2) = tipos r1 in     (*Trata o (TIPO -> TIPO)*)
                      let (t2, r3) = tipos r2 in 
                      begin match r3 with
                        | LParen :: r4 -> (TFunc (t1,t2), r4)
                        | _ -> failwith "!"
                      end)
  | Arrow :: r1 -> tipos r1 (*Chama recursivamente para pegar o tipo que existe após a seta*)
  | Bool :: r1 -> (TBool, r1)
  | Nat :: r1 -> (TNat, r1)
  | _ -> failwith "!"
;;

(*Agora podemos converter, finalmente, simbolos para termos *)
(*Atenção para o retorno: (termo, restante da lista de simbolos) *)
let rec converter_para_termos (simbolos: simbolo list): (termo * simbolo list) =
  begin match simbolos with
  | LParen :: r1 -> ( let (t1, r2) = converter_para_termos r1 in (*Para pegar o primeiro termo*)
                      let (t2, r3) = converter_para_termos r2 in (*Para pegar o segundo termo*)
                      begin match r3 with
                      | RParen :: r4 -> (Appl (t1,t2), r4) (*Caso: (Termo Termo) válido*)
                      | _ -> failwith "!" (*Termo inválido*)
                      end )
  | RParen :: _ -> failwith "!" (*Trivial que ")" so é valido se for encontrado após um "(" como acima, Caso do LParen*)
  | If :: r1 -> ( let (t1,r2) = converter_para_termos r1 in (*Para pegar o termo imediatamente após o "if"*)
                  begin match r2 with
                  | Then :: r3 -> (let (t2, r4) = converter_para_termos r3 in (*Para pegar o termo imediatamente após o "then"*)
                                   begin match r4 with
                                   | Else :: r5 -> (let (t3, r6) = converter_para_termos r5 in (*Para pegar o termo imediatamente após o "else"*)
                                                    begin match r6 with
                                                    | Endif :: r7 -> (If (t1,t2,t3), r7)
                                                    | _ -> failwith "!"
                                                    end              )
                                   | _ -> failwith "!"
                                   end              )
                  | _ -> failwith "!" 
                  end      )
  | True :: r1 -> (True, r1)
  | False :: r1 -> (False, r1)
  | Suc :: r1 -> (Suc, r1)
  | EhZero :: r1 -> (EhZero, r1)
  | Pred :: r1 -> (Pred, r1)
  | Lambda :: Variavel v :: Colon :: r1 -> (let (t1, r2) = tipos r1 in (*temos um tipo nesse local, o tipo da variavel*)
                                        begin match r2 with
                                          | Dot :: r3 -> (let (t2, r4) = converter_para_termos r3 in (*Converte para termo o simbolo entre o "." e o "                                                                                                                                      end"*)
                                                          begin match r4 with
                                                            | End :: r5 -> (Lamb (Var v, t1, t2), r5) (*Transforma todo o lambda em termo*)
                                                            | _ -> failwith "!"
                                                          end)
                                          | _ -> failwith "!"
                                        end)
  | Numero :: r1 -> (Numero, r1)
  | Variavel v :: r1 -> (Var (Var v), r1) (*Transforma a variavel em tipo variavel de fato*)
  | _ -> failwith "!"
  end
;;

(*Cuida de imprimir de forma correta a saida esperada pelo enunciado do trabalho*)
let printar_saida tipo =
  let rec aux restante =
    match restante with
    | TNat -> "Nat"
    | TBool -> "Bool"
    | TFunc (t1,t2) -> (let t3 = aux t1 in 
                        let t4 = aux t2 in 
                        "( " ^ t3 ^ " -> " ^ t4 ^ " )" )
    | Sem_tipo_determinado -> failwith "-" (*Caso especial esperado segundo o enunciado do trabalho*)
  in
  let resposta = aux tipo in 
  print_endline resposta
;;

let () =
  try
    let list_inicial = recebe_entrada (read_line()) in
    let list_simbolos = analise_lexica list_inicial in
    let (termo_lido, restante_simbolos) = converter_para_termos list_simbolos in
    if restante_simbolos <> [] then failwith "!" (*O esperado é que a entrada por completo esteja no formato de termo em "termo_lido"*)
    else begin 
      let resposta = tipagem termo_lido [] in (*O contexto começa vazio*)
      printar_saida resposta (*Imprime a resposta esperada*)
    end
  with
  | Failure msg -> Printf.printf "%s\n" msg (*Aqui vai ser jogado o "!" e o "-"*)
;;  