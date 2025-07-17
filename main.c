#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Enums e structs
typedef enum {
    VARIAVEL,
    NEGACAO,
    CONJUNCAO,
    DISJUNCAO,
    IMPLICACAO,
    BICONDICIONAL
} SimboloLogico;


typedef struct Formula {
    SimboloLogico tipoSimbolo;
    char *variavel;
    // Caso a operação seja unária, direita será NULL
    // Caso a operação seja binária, esquerda e direita serão preenchidas
    // Caso a operação seja uma variável, esquerda e direita serão NULL
    struct Formula *esquerda;
    struct Formula *direita;
} Formula;

typedef struct Variavel{
    char* nome;
    bool valor;
} Variavel;

typedef struct ListaDeVariaveis {
    Variavel* itens;
    size_t quantidade;
    size_t capacidade;
} ListaDeVariaveis;

typedef struct Linha{
    Formula* f;
    ListaDeVariaveis lista;
} Linha;

// Ponteiro que representa a posição atual na linha
static char *pos_atual;



// Funções auxiliares
void pular_espacos() {
    while (isspace(*pos_atual)) {
        pos_atual++;
    }
}
void limpar_formula(Formula* f) {
    if (f == NULL) {
        return;
    }
    limpar_formula(f->esquerda);
    limpar_formula(f->direita);
    if (f->variavel) {
        free(f->variavel);
    }
    free(f);
}
void limpar_lista_variaveis(ListaDeVariaveis* lista) {
    if (lista == NULL) return;
    for (int i = 0; i < lista->quantidade; i++) {
        free(lista->itens[i].nome);
    }
    free(lista->itens);
    lista->itens = NULL;
    lista->quantidade = 0;
    lista->capacidade = 0;
}



// Função para contar as variáveis
void append_se_n_existe(ListaDeVariaveis* lista, const char* nome_var) {

    for (int i = 0; i < lista->quantidade; i++) {
        //Verifica se a variável de mesmo nome já existe
        if (strcmp(lista->itens[i].nome, nome_var) == 0) {
            return;
        }
    }

    if (lista->quantidade >= lista->capacidade) {
        lista->capacidade *= 2; // Dobra o tamanho ao invés de incrementar 1 por 1 para otimizar 
        lista->itens = (Variavel*)realloc(lista->itens, lista->capacidade * sizeof(Variavel));
        if (lista->itens == NULL) {
            perror("Falha ao realocar lista de variaveis");
            exit(1);
        }
    }

    lista->itens[lista->quantidade].nome = strdup(nome_var);
    lista->itens[lista->quantidade].valor = false;
    lista->quantidade++;
}

// Funções que criam cada tipo esecífico de fórmula
Formula* criar_variavel(const char* inicio, int tamanho, ListaDeVariaveis* lista) {
    Formula* f = (Formula*)malloc(sizeof(Formula));
    if (f == NULL) {
        perror("Falha ao alocar memória");
        exit(1);
    }
    f->tipoSimbolo = VARIAVEL;
    f->variavel = strndup(inicio, tamanho);
    f->esquerda = NULL;
    f->direita = NULL;
    //Adiciona a variável à lista de variáveis se ainda não tiver sido adicionada
    append_se_n_existe(lista, f->variavel);

    return f;
}

Formula* criar_unario(SimboloLogico tipo, Formula* filho) {
    Formula* f = (Formula*)malloc(sizeof(Formula));
    if (f == NULL) {
        perror("Falha ao alocar memória");
        exit(1);
    }
    f->tipoSimbolo = tipo;
    f->variavel = NULL;
    f->esquerda = filho;
    f->direita = NULL;
    return f;
}

Formula* criar_binario(SimboloLogico tipo, Formula* esq, Formula* dir) {
    Formula* f = (Formula*)malloc(sizeof(Formula));
    if (f == NULL) {
        perror("Falha ao alocar memória");
        exit(1);
    }
    f->tipoSimbolo = tipo;
    f->variavel = NULL;
    f->esquerda = esq;
    f->direita = dir;
    return f;
}



// Verificação da satisfatiblidade

static bool post_order_valoracao(Formula* f, ListaDeVariaveis* lista) {
    if (f->tipoSimbolo == VARIAVEL) {
        for (uint8_t i = 0; i < lista->quantidade; i++) {
            if (strcmp(f->variavel, lista->itens[i].nome) == 0) {
                return lista->itens[i].valor;
            }
        }
        return false;
    }

    bool v_esq = (f->esquerda != NULL) ? post_order_valoracao(f->esquerda, lista) : false;

    if (f->tipoSimbolo == NEGACAO) {
        return !v_esq;
    }

    bool v_dir = (f->direita != NULL) ? post_order_valoracao(f->direita, lista) : false;

    switch (f->tipoSimbolo) {
        case CONJUNCAO:
            return v_esq && v_dir;
        case DISJUNCAO:
            return v_esq || v_dir;
        case IMPLICACAO:
            return !v_esq || v_dir;
        case BICONDICIONAL:
            return v_esq == v_dir;
        default: return false;
    }
}

void verifica_sats(Linha linha, FILE* arquivo_saida) {
    if (linha.f == NULL) {
        fprintf(arquivo_saida, "NAO, []\n");
        return;
    }
    // Cria um inteiro que vai armazenar o número de combinações possíveis
    // 1 << n = 2^n
    uint32_t num_combinacoes = (uint32_t)1 << linha.lista.quantidade;
    // 001 vai ser VFF já que i = 1, ai pra 1 vai ser o j = 0, 0 vai ser j = 1 e o último 0 vai ser j = 2
    for (uint32_t i = 0; i < num_combinacoes; i++) {
        for (size_t j = 0; j < linha.lista.quantidade; j++) {
            linha.lista.itens[j].valor = (i >> j) & 1;
        }

        if (post_order_valoracao(linha.f, &linha.lista)) {
            fprintf(arquivo_saida, "SIM, [");
            for (int k = 0; k < linha.lista.quantidade; k++) {
                fprintf(arquivo_saida, "[%s,%c]", linha.lista.itens[k].nome,linha.lista.itens[k].valor ? 'V' : 'F');
                if (k < linha.lista.quantidade - 1) {
                    fprintf(arquivo_saida, ",");
                }
            }
            fprintf(arquivo_saida, "]\n");
            return;
        }
    }

    fprintf(arquivo_saida, "NAO, []\n");
}



// Parser

static Formula* parser_recursivo(ListaDeVariaveis* lista);

//Função que prepara o parser a chama a função recursiva
Linha parser_init(char *texto_formula) {
    Linha resultado;
    resultado.f = NULL;

    resultado.lista.quantidade = 0;
    resultado.lista.capacidade = 8;
    resultado.lista.itens = (Variavel*)malloc(resultado.lista.capacidade * sizeof(Variavel));
    if (resultado.lista.itens == NULL) {
        perror("Falha ao alocar lista inicial de vars");
        exit(1);
    }

    if (texto_formula == NULL || *texto_formula == '\0') {
        return resultado;
    }

    pos_atual = texto_formula;
    resultado.f = parser_recursivo(&resultado.lista);

    return resultado;
}

static Formula* parser_recursivo(ListaDeVariaveis* lista) {
    pular_espacos();

    if (isalpha(*pos_atual)) {
        const char* inicio_var = pos_atual;
        while (isalnum(*pos_atual)) {
            pos_atual++;
        }
        return criar_variavel(inicio_var, pos_atual - inicio_var, lista);
    }

    if (*pos_atual == '~') {
        pos_atual++;
        Formula* filho = parser_recursivo(lista);
        return criar_unario(NEGACAO, filho);
    }

    if (*pos_atual == '(') {
        pos_atual++;

        Formula* f = parser_recursivo(lista);
        pular_espacos();

        if (*pos_atual == ')') {
            pos_atual++;
            return f;
        }

        Formula* esq = f;
        SimboloLogico tipo_op;

        if (strncmp(pos_atual, "<->", 3) == 0) {
            tipo_op = BICONDICIONAL;
            pos_atual += 3;
        } else if (strncmp(pos_atual, "->", 2) == 0) {
            tipo_op = IMPLICACAO;
            pos_atual += 2;
        } else if (*pos_atual == '&') {
            tipo_op = CONJUNCAO;
            pos_atual++;
        } else if (*pos_atual == '|') {
            tipo_op = DISJUNCAO;
            pos_atual++;
        }

        Formula* dir = parser_recursivo(lista);

        pular_espacos();

        pos_atual++; // Pula o ) final

        return criar_binario(tipo_op, esq, dir);
    }

    fprintf(stderr, "Erro: caractere inesperado '%c'.\n", *pos_atual);
    return NULL;

}



int main(void) {
    FILE *arquivo_entrada = fopen("data.txt", "r");
    char *texto_linha = NULL;
    size_t tamanho = 0;
    // Abre o arquivo de entrada
    if (arquivo_entrada == NULL) {
        perror("Erro ao abrir o arquivo de entrada 'data.txt'");
        return 1;
    }
    // Cria ou abre o arquivo de saída
    FILE *arquivo_saida = fopen("saida.txt", "w");
    if (arquivo_saida == NULL) {
        perror("Erro ao criar/abrir o arquivo 'saida.txt'");
        fclose(arquivo_entrada);
        return 1;
    }

    while (getline(&texto_linha, &tamanho, arquivo_entrada) > 1) {
        //Transforma a linha em uma fórmula (árvore)
        Linha linha = parser_init(texto_linha);
        if (linha.f != NULL) {
            //Verifica a satisfatibilidade da fórmula
            verifica_sats(linha, arquivo_saida);
            limpar_formula(linha.f);
            limpar_lista_variaveis(&linha.lista);
        } else {
            fprintf(arquivo_saida, "Linha inválida: %s ", texto_linha);
        }
    }

    fclose(arquivo_entrada);
    fclose(arquivo_saida);
    free(texto_linha);

    return 0;
}
