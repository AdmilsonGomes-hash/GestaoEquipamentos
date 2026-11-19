import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Scanner;

/**
 * SISTEMA DE GESTÃO DE EQUIPAMENTOS DE UM LABORATÓRIO DE INFORMÁTICA
 * Seminário de Algoritmos e Estruturas de Dados I - Tabelas de Espalhamento (Hash Tables)
 *
 * Elaborado por: Admilson Mateus Gomes, Nlando Castigo e Nkenda Joaquim Sumbula
 *
 * Esta aplicação implementa uma tabela de espalhamento
 * com CINCO estratégias de resolução de colisões:
 *
 *   1) Encadeamento separado (listas ligadas externas em cada posição);
 *   2) Encadeamento coalescido (listas ligadas internas no próprio vector via índices);
 *   3) Endereçamento aberto com sondagem LINEAR      h(k,i) = (h1(k) + i)      mod m;
 *   4) Endereçamento aberto com sondagem QUADRÁTICA  h(k,i) = (h1(k) + i^2)    mod m;
 *   5) Endereçamento aberto com DUPLO ESPALHAMENTO   h(k,i) = (h1(k) + i*h2(k)) mod m.
 */
public class GestaoEquipamentos {
    // 1. Declaração de Constantes
    static final int BASE_H1 = 31;
    static final int BASE_H2 = 37;
    static final int TAMANHO_INICIAL = 11;
    static final double LIMITE_ENCADEAMENTO = 0.75;
    static final double LIMITE_ENDERECAMENTO = 0.50;
    static final String FICHEIRO_PADRAO = "inventario_equipamentos.csv";
    static boolean mostrarAvisoRehash = true;
    static final String[] ESTADOS = {"Operacional", "Em reparação", "Avariado"};
    static final String[] CATEGORIAS = {"Computador", "Monitor", "Router", "Switch",
            "Projector", "Impressora", "Outro"};
    // 2. FUNÇÕES AUXILIARES (números primos e função hash)
    static boolean ePrimo(int x) {
        if (x < 2) return false;
        if (x % 2 == 0) return x == 2;
        for (int d = 3; (long) d * d <= x; d += 2) {
            if (x % d == 0) return false;
        }
        return true;
    }
    static int proximoPrimo(int x) {
        while (!ePrimo(x)) x++;
        return x;
    }

    static int hash(String chave, int base, int modulo, boolean mostrar) {
        long h = 0;
        for (int i = 0; i < chave.length(); i++) {
            char c = chave.charAt(i);
            long anterior = h;
            h = (h * base + c) % modulo;
            if (mostrar) {
                System.out.println("        '" + c + "' (ASCII " + (int) c + "): ("
                        + anterior + " x " + base + " + " + (int) c + ") mod " + modulo
                        + " = " + h);
            }
        }
        return (int) h;
    }

    // 3. ENTIDADE: EQUIPAMENTO (chave + dados satélite)
    static class Equipamento {
        private final String codigo;
        private String designacao;
        private String categoria;
        private String estado;
        private String localizacao;
        Equipamento(String codigo, String designacao, String categoria,
                    String estado, String localizacao) {
            this.codigo = codigo;
            this.designacao = designacao;
            this.categoria = categoria;
            this.estado = estado;
            this.localizacao = localizacao;
        }

        String getCodigo()      { return codigo; }
        String getDesignacao()  { return designacao; }
        String getCategoria()   { return categoria; }
        String getEstado()      { return estado; }
        String getLocalizacao() { return localizacao; }
        void setEstado(String novoEstado) { this.estado = novoEstado; }

        // Serializa o equipamento para uma linha CSV separada por ponto e vírgula.
        String paraLinhaCSV() {
            return limparSeparador(codigo) + ";"
                    + limparSeparador(designacao) + ";"
                    + limparSeparador(categoria) + ";"
                    + limparSeparador(estado) + ";"
                    + limparSeparador(localizacao);
        }
        // Reconstrói um Equipamento a partir de uma linha CSV.
        static Equipamento deLinhaCSV(String linha) {
            String[] partes = linha.split(";", -1);
            if (partes.length < 5) return null;
            String cod = partes[0].trim().toUpperCase();
            if (cod.isEmpty()) return null;
            return new Equipamento(cod, partes[1].trim(), partes[2].trim(),
                    partes[3].trim(), partes[4].trim());
        }

        private static String limparSeparador(String s) {
            return (s == null) ? "" : s.replace(";", ",").trim();
        }

        static String cabecalho() {
            return String.format("%-8s | %-26s | %-11s | %-12s | %s",
                    "Código", "Designação", "Categoria", "Estado", "Localização");
        }

        @Override
        public String toString() {
            return String.format("%-8s | %-26s | %-11s | %-12s | %s",
                    codigo, designacao, categoria, estado, localizacao);
        }
    }
    // 4. CLASSE ABSTRACTA: o que é comum a todas as tabelas
    static abstract class TabelaHash {
        protected int m;
        protected int n;
        protected final double limiteCarga;
        protected long colisoes;
        protected long comparacoes;
        protected int rehashes;
        protected boolean detalhado;

        TabelaHash(int tamanhoInicial, double limiteCarga) {
            this.m = proximoPrimo(Math.max(tamanhoInicial, 5));
            this.n = 0;
            this.limiteCarga = limiteCarga;
        }

        abstract String nome();
        abstract boolean inserir(Equipamento e);
        abstract Equipamento pesquisar(String codigo);
        abstract boolean remover(String codigo);
        abstract List<Equipamento> todos();
        abstract void mostrarEstrutura();
        abstract void estatisticasEspecificas();

        void setDetalhado(boolean d) { this.detalhado = d; }
        boolean isDetalhado()        { return detalhado; }
        int getN()                   { return n; }
        int getM()                   { return m; }
        int getRehashes()            { return rehashes; }
        long getColisoes()           { return colisoes; }
        long getComparacoes()        { return comparacoes; }
        double factorCarga()         { return (double) n / m; }

        protected int hash1(String chave) {
            if (detalhado) {
                System.out.println("      Cálculo de h1(\"" + chave + "\") com m = " + m
                        + " (regra de Horner, base " + BASE_H1 + "):");
            }
            int h = hash(chave, BASE_H1, m, detalhado);
            if (detalhado) System.out.println("      => h1 = " + h);
            return h;
        }

        boolean actualizarEstado(String codigo, String novoEstado) {
            boolean det = detalhado;
            detalhado = false;
            Equipamento e = pesquisar(codigo);
            detalhado = det;
            if (e == null) return false;
            e.setEstado(novoEstado);
            return true;
        }

        void estatisticas() {
            System.out.println("  Método .................. " + nome());
            System.out.println("  Tamanho da tabela (m) ... " + m);
            System.out.println("  Equipamentos (n) ........ " + n);
            System.out.println(String.format("  Factor de carga (n/m) ... %.3f  (limite do rehash: %.2f)",
                    factorCarga(), limiteCarga));
            System.out.println("  Colisões acumuladas ..... " + colisoes);
            System.out.println("  Comparações de chaves ... " + comparacoes);
            System.out.println("  Redimensionamentos ...... " + rehashes);
            estatisticasEspecificas();
        }

        protected void avisoRehash(int antigo, int novo, double carga) {
            if (!mostrarAvisoRehash) return;
            if (novo == antigo) {
                System.out.println(String.format(
                        "  >>> LIMPEZA: factor de carga %.3f (com lápides) excedeu %.2f. "
                                + "A tabela foi reconstruída com o mesmo m = %d (lápides eliminadas).",
                        carga, limiteCarga, novo));
                return;
            }
            System.out.println(String.format(
                    "  >>> REHASH: factor de carga %.3f excedeu o limite %.2f. "
                            + "A tabela passou de m = %d para m = %d (todos os equipamentos foram reinseridos).",
                    carga, limiteCarga, antigo, novo));
        }
    }
    // 5A. ENCADEAMENTO SEPARADO (listas ligadas externas)
    static class TabelaEncadeada extends TabelaHash {
        private static class No {
            Equipamento dado;
            No seguinte;
            No(Equipamento dado, No seguinte) {
                this.dado = dado;
                this.seguinte = seguinte;
            }
        }

        private No[] tabela;
        TabelaEncadeada(int tamanhoInicial) {
            super(tamanhoInicial, LIMITE_ENCADEAMENTO);
            this.tabela = new No[m];
        }

        @Override
        String nome() { return "Encadeamento separado"; }

        @Override
        boolean inserir(Equipamento e) {
            boolean ok = inserirInterno(e);
            if (ok && factorCarga() > limiteCarga) {
                redimensionar();
            }
            return ok;
        }

        private boolean inserirInterno(Equipamento e) {
            String chave = e.getCodigo();
            int idx = hash1(chave);
            if (detalhado) System.out.println("      Posição calculada: T[" + idx + "]");

            No p = tabela[idx];
            while (p != null) {
                comparacoes++;
                if (p.dado.getCodigo().equals(chave)) {
                    if (detalhado) System.out.println("      A chave já existe nesta lista. Inserção recusada.");
                    return false;
                }
                p = p.seguinte;
            }

            if (tabela[idx] != null) {
                colisoes++;
                if (detalhado) System.out.println("      COLISÃO: T[" + idx
                        + "] já tem elementos. O novo equipamento entra no início da lista.");
            } else if (detalhado) {
                System.out.println("      Posição livre: cria-se uma lista com 1 elemento.");
            }
            tabela[idx] = new No(e, tabela[idx]);
            n++;
            return true;
        }

        @Override
        Equipamento pesquisar(String codigo) {
            int idx = hash1(codigo);
            if (detalhado) System.out.println("      Percorrer a lista de T[" + idx + "]:");
            No p = tabela[idx];
            while (p != null) {
                comparacoes++;
                if (detalhado) System.out.println("        comparar com " + p.dado.getCodigo());
                if (p.dado.getCodigo().equals(codigo)) return p.dado;
                p = p.seguinte;
            }
            if (detalhado) System.out.println("        fim da lista (não encontrado).");
            return null;
        }

        @Override
        boolean remover(String codigo) {
            int idx = hash1(codigo);
            No anterior = null;
            No p = tabela[idx];
            while (p != null) {
                comparacoes++;
                if (p.dado.getCodigo().equals(codigo)) {
                    if (anterior == null) tabela[idx] = p.seguinte;
                    else anterior.seguinte = p.seguinte;
                    n--;
                    if (detalhado) System.out.println("      Nó removido da lista de T[" + idx + "].");
                    return true;
                }
                anterior = p;
                p = p.seguinte;
            }
            return false;
        }

        @Override
        List<Equipamento> todos() {
            List<Equipamento> lista = new ArrayList<Equipamento>();
            for (int i = 0; i < m; i++) {
                for (No p = tabela[i]; p != null; p = p.seguinte) lista.add(p.dado);
            }
            return lista;
        }

        private void redimensionar() {
            List<Equipamento> lista = todos();
            int antigo = m;
            double carga = factorCarga();
            long c = colisoes, cmp = comparacoes;
            boolean det = detalhado;
            detalhado = false;

            m = proximoPrimo(2 * m + 1);
            tabela = new No[m];
            n = 0;
            for (Equipamento e : lista) inserirInterno(e);

            colisoes = c;
            comparacoes = cmp;
            detalhado = det;
            rehashes++;
            avisoRehash(antigo, m, carga);
        }

        @Override
        void mostrarEstrutura() {
            System.out.println("  Tabela com " + m + " posições (cada posição guarda uma lista externa):");
            for (int i = 0; i < m; i++) {
                StringBuilder sb = new StringBuilder();
                sb.append(String.format("  T[%2d] ", i));
                if (tabela[i] == null) {
                    sb.append("(vazio)");
                } else {
                    for (No p = tabela[i]; p != null; p = p.seguinte) {
                        sb.append(p.dado.getCodigo());
                        if (p.seguinte != null) sb.append(" -> ");
                    }
                }
                System.out.println(sb.toString());
            }
        }

        @Override
        void estatisticasEspecificas() {
            int vazias = 0, maior = 0;
            for (int i = 0; i < m; i++) {
                int comp = 0;
                for (No p = tabela[i]; p != null; p = p.seguinte) comp++;
                if (comp == 0) vazias++;
                if (comp > maior) maior = comp;
            }
            System.out.println("  Posições vazias ......... " + vazias + " de " + m);
            System.out.println("  Maior lista ............. " + maior + " elemento(s)");
        }
    }
    // 5B. ENCADEAMENTO COALESCIDO (listas ligadas internas no vector)
    static class TabelaEncadeamentoCoalescido extends TabelaHash {
        private Equipamento[] tabela;
        private int[] proximo; // índice do próximo elemento da cadeia (-1 = fim da cadeia)
        private int cursorLivre;
        TabelaEncadeamentoCoalescido(int tamanhoInicial) {
            super(tamanhoInicial, LIMITE_ENCADEAMENTO);
            iniciarArrays(m);
        }

        private void iniciarArrays(int tam) {
            this.tabela = new Equipamento[tam];
            this.proximo = new int[tam];
            for (int i = 0; i < tam; i++) {
                this.proximo[i] = -1;
            }
            this.cursorLivre = tam - 1;
        }

        @Override
        String nome() { return "Encadeamento coalescido (interno)"; }
        private int obterPosicaoLivre() {
            while (cursorLivre >= 0 && tabela[cursorLivre] != null) {
                cursorLivre--;
            }
            return cursorLivre;
        }

        @Override
        boolean inserir(Equipamento e) {
            boolean ok = inserirInterno(e);
            if (ok && factorCarga() > limiteCarga) {
                redimensionar();
            }
            return ok;
        }
        private boolean inserirInterno(Equipamento e) {
            String chave = e.getCodigo();
            int idx = hash1(chave);
            // Posição base livre
            if (tabela[idx] == null) {
                tabela[idx] = e;
                proximo[idx] = -1;
                n++;
                if (detalhado) System.out.println("      Posição base T[" + idx + "] livre: inserido directamente.");
                return true;
            }
            // Percorrer cadeia existente para verificar duplicados e achar o fim
            int atual = idx;
            while (true) {
                comparacoes++;
                if (tabela[atual].getCodigo().equals(chave)) {
                    if (detalhado) System.out.println("      A chave já existe na cadeia. Inserção recusada.");
                    return false;
                }
                if (proximo[atual] == -1) break;
                atual = proximo[atual];
            }

            // Alocar posição livre a partir do fim da tabela e encadear
            int livre = obterPosicaoLivre();
            if (livre == -1) return false;
            colisoes++;
            tabela[livre] = e;
            proximo[livre] = -1;
            proximo[atual] = livre;
            n++;
            if (detalhado) {
                System.out.println("      COLISÃO em T[" + idx + "]: guardado em T[" + livre
                        + "] e encadeado após T[" + atual + "].");
            }
            return true;
        }

        @Override
        Equipamento pesquisar(String codigo) {
            int atual = hash1(codigo);
            if (tabela[atual] == null) return null;
            while (atual != -1) {
                comparacoes++;
                if (detalhado) System.out.println("      Verificar T[" + atual + "] (" + tabela[atual].getCodigo() + ")");
                if (tabela[atual].getCodigo().equals(codigo)) return tabela[atual];
                atual = proximo[atual];
            }
            return null;
        }

        @Override
        boolean remover(String codigo) {
            // Para manter a integridade das cadeias coalescidas sem partir ligações,
            // reconstrói-se a tabela sem o elemento removido.
            List<Equipamento> todos = todos();
            boolean encontrado = false;
            List<Equipamento> restantes = new ArrayList<Equipamento>();
            for (Equipamento eq : todos) {
                comparacoes++;
                if (eq.getCodigo().equals(codigo)) {
                    encontrado = true;
                } else {
                    restantes.add(eq);
                }
            }
            if (!encontrado) return false;
            long c = colisoes, cmp = comparacoes;
            boolean det = detalhado;
            detalhado = false;
            iniciarArrays(m);
            n = 0;
            for (Equipamento eq : restantes) inserirInterno(eq);
            colisoes = c;
            comparacoes = cmp;
            detalhado = det;
            if (detalhado) System.out.println("      Equipamento removido e cadeias internas reorganizadas.");
            return true;
        }

        @Override
        List<Equipamento> todos() {
            List<Equipamento> lista = new ArrayList<Equipamento>();
            for (int i = 0; i < m; i++) {
                if (tabela[i] != null) lista.add(tabela[i]);
            }
            return lista;
        }
        private void redimensionar() {
            List<Equipamento> lista = todos();
            int antigo = m;
            double carga = factorCarga();
            long c = colisoes, cmp = comparacoes;
            boolean det = detalhado;
            detalhado = false;

            m = proximoPrimo(2 * m + 1);
            iniciarArrays(m);
            n = 0;
            for (Equipamento e : lista) inserirInterno(e);
            colisoes = c;
            comparacoes = cmp;
            detalhado = det;
            rehashes++;
            avisoRehash(antigo, m, carga);
        }

        @Override
        void mostrarEstrutura() {
            System.out.println("  Tabela com " + m + " posições (encadeamento interno via índice 'prox'):");
            for (int i = 0; i < m; i++) {
                if (tabela[i] == null) {
                    System.out.println(String.format("  T[%2d] (vazio)", i));
                } else {
                    String proxStr = (proximo[i] == -1) ? "FIM" : "T[" + proximo[i] + "]";
                    System.out.println(String.format("  T[%2d] %-8s -> prox: %s",
                            i, tabela[i].getCodigo(), proxStr));
                }
            }
        }

        @Override
        void estatisticasEspecificas() {
            int vazias = 0, encadeados = 0;
            for (int i = 0; i < m; i++) {
                if (tabela[i] == null) vazias++;
                else if (proximo[i] != -1) encadeados++;
            }
            System.out.println("  Posições vazias ......... " + vazias + " de " + m);
            System.out.println("  Nós com apontador prox .. " + encadeados);
        }
    }
    // 6. ENDEREÇAMENTO ABERTO (linear, quadrático, duplo espalhamento)
    static class TabelaEnderecamentoAberto extends TabelaHash {
        enum Sondagem { LINEAR, QUADRATICA, DUPLA }
        private static final int VAZIA = 0;
        private static final int OCUPADA = 1;
        private static final int APAGADA = 2;
        private final Sondagem tipo;
        private Equipamento[] tabela;
        private int[] marca;
        private int apagadas;
        TabelaEnderecamentoAberto(int tamanhoInicial, Sondagem tipo) {
            super(tamanhoInicial, LIMITE_ENDERECAMENTO);
            this.tipo = tipo;
            this.tabela = new Equipamento[m];
            this.marca = new int[m];
            this.apagadas = 0;
        }

        @Override
        String nome() {
            switch (tipo) {
                case LINEAR:     return "Endereçamento aberto - sondagem linear";
                case QUADRATICA: return "Endereçamento aberto - sondagem quadrática";
                default:         return "Endereçamento aberto - duplo espalhamento";
            }
        }
        private int hash2(String chave) {
            if (detalhado) {
                System.out.println("      Cálculo de h2(\"" + chave + "\") = 1 + (hash mod " + (m - 1) + "):");
            }
            int h = 1 + hash(chave, BASE_H2, m - 1, detalhado);
            if (detalhado) System.out.println("      => h2 = " + h);
            return h;
        }

        private int posicao(int h1, int h2, int i) {
            long idx;
            switch (tipo) {
                case LINEAR:     idx = (long) h1 + i; break;
                case QUADRATICA: idx = (long) h1 + (long) i * i; break;
                default:         idx = (long) h1 + (long) i * h2; break;
            }
            return (int) (idx % m);
        }
        private String formula(int h1, int h2, int i) {
            switch (tipo) {
                case LINEAR:     return "(" + h1 + " + " + i + ") mod " + m;
                case QUADRATICA: return "(" + h1 + " + " + i + "^2) mod " + m;
                default:         return "(" + h1 + " + " + i + " x " + h2 + ") mod " + m;
            }
        }

        @Override
        boolean inserir(Equipamento e) {
            boolean ok = inserirInterno(e);
            if (ok && (double) (n + apagadas) / m > limiteCarga) {
                redimensionar();
            }
            return ok;
        }
        private boolean inserirInterno(Equipamento e) {
            String chave = e.getCodigo();
            int h1 = hash1(chave);
            int h2 = (tipo == Sondagem.DUPLA) ? hash2(chave) : 0;
            int primeiraApagada = -1;
            int destino = -1;
            int ocupadasVistas = 0;

            for (int i = 0; i < m; i++) {
                int idx = posicao(h1, h2, i);
                String f = formula(h1, h2, i);
                if (marca[idx] == VAZIA) {
                    if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx + " -> livre.");
                    destino = (primeiraApagada != -1) ? primeiraApagada : idx;
                    break;
                } else if (marca[idx] == APAGADA) {
                    if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                            + " -> posição APAGADA.");
                    if (primeiraApagada == -1) primeiraApagada = idx;
                } else {
                    comparacoes++;
                    if (tabela[idx].getCodigo().equals(chave)) {
                        if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                                + " -> a chave já existe. Inserção recusada.");
                        return false;
                    }
                    ocupadasVistas++;
                    if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                            + " -> OCUPADA por " + tabela[idx].getCodigo() + " (COLISÃO).");
                }
            }
            if (destino == -1) destino = primeiraApagada;
            if (destino == -1) {
                System.out.println("  ERRO: não foi encontrada nenhuma posição livre (tabela cheia).");
                return false;
            }
            if (marca[destino] == APAGADA) apagadas--;
            tabela[destino] = e;
            marca[destino] = OCUPADA;
            n++;
            colisoes += ocupadasVistas;
            if (detalhado) System.out.println("      Equipamento guardado em T[" + destino + "].");
            return true;
        }

        private int localizar(String chave) {
            int h1 = hash1(chave);
            int h2 = (tipo == Sondagem.DUPLA) ? hash2(chave) : 0;
            for (int i = 0; i < m; i++) {
                int idx = posicao(h1, h2, i);
                String f = formula(h1, h2, i);
                if (marca[idx] == VAZIA) {
                    if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                            + " -> posição VAZIA: a chave não existe.");
                    return -1;
                }
                if (marca[idx] == APAGADA) {
                    if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                            + " -> APAGADA: continuar a sondagem.");
                    continue;
                }
                comparacoes++;
                if (tabela[idx].getCodigo().equals(chave)) {
                    if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                            + " -> ENCONTRADO (" + chave + ").");
                    return idx;
                }
                if (detalhado) System.out.println("      Tentativa i=" + i + ": " + f + " = " + idx
                        + " -> ocupada por " + tabela[idx].getCodigo() + " (outra chave): continuar.");
            }
            return -1;
        }

        @Override
        Equipamento pesquisar(String codigo) {
            int idx = localizar(codigo);
            return (idx == -1) ? null : tabela[idx];
        }

        @Override
        boolean remover(String codigo) {
            int idx = localizar(codigo);
            if (idx == -1) return false;
            tabela[idx] = null;
            marca[idx] = APAGADA;
            n--;
            apagadas++;
            if (detalhado) System.out.println("      T[" + idx + "] marcada como APAGADA (lápide).");
            return true;
        }

        @Override
        List<Equipamento> todos() {
            List<Equipamento> lista = new ArrayList<Equipamento>();
            for (int i = 0; i < m; i++) {
                if (marca[i] == OCUPADA) lista.add(tabela[i]);
            }
            return lista;
        }

        private void redimensionar() {
            List<Equipamento> lista = todos();
            int antigo = m;
            double carga = (double) (n + apagadas) / m;
            long c = colisoes, cmp = comparacoes;
            boolean det = detalhado;
            detalhado = false;
            if ((double) n / m > limiteCarga / 2) m = proximoPrimo(2 * m + 1);
            tabela = new Equipamento[m];
            marca = new int[m];
            apagadas = 0;
            n = 0;
            for (Equipamento e : lista) inserirInterno(e);
            colisoes = c;
            comparacoes = cmp;
            detalhado = det;
            rehashes++;
            avisoRehash(antigo, m, carga);
        }

        @Override
        void mostrarEstrutura() {
            System.out.println("  Tabela com " + m + " posições (uma posição = um equipamento):");
            for (int i = 0; i < m; i++) {
                StringBuilder sb = new StringBuilder();
                sb.append(String.format("  T[%2d] ", i));
                if (marca[i] == VAZIA) {
                    sb.append("(vazio)");
                } else if (marca[i] == APAGADA) {
                    sb.append("<APAGADA>");
                } else {
                    int base = hash(tabela[i].getCodigo(), BASE_H1, m, false);
                    sb.append(String.format("%-8s (h1 = %d%s)", tabela[i].getCodigo(), base,
                            base == i ? ", posição base" : ", deslocado"));
                }
                System.out.println(sb.toString());
            }
        }

        @Override
        void estatisticasEspecificas() {
            int inicio = -1;
            for (int i = 0; i < m && inicio == -1; i++) {
                if (marca[i] == VAZIA) inicio = i;
            }
            int maior = 0, atual = 0;
            if (inicio == -1) {
                maior = m;
            } else {
                for (int k = 1; k <= m; k++) {
                    int i = (inicio + k) % m;
                    if (marca[i] != VAZIA) {
                        atual++;
                        if (atual > maior) maior = atual;
                    } else {
                        atual = 0;
                    }
                }
            }
            System.out.println("  Posições APAGADAS ....... " + apagadas);
            System.out.println("  Maior aglomerado ........ " + maior + " posições consecutivas não vazias");
        }
    }
    // 7. DADOS DE DEMONSTRAÇÃO E PERSISTÊNCIA EM FICHEIRO
    static List<Equipamento> dadosDemonstracao() {
        List<Equipamento> d = new ArrayList<Equipamento>();
        d.add(new Equipamento("PC01", "Computador Dell OptiPlex", "Computador", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("PC02", "Computador Dell OptiPlex", "Computador", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("PC03", "Computador Dell OptiPlex", "Computador", "Em reparação", "Laboratório 1"));
        d.add(new Equipamento("PC04", "Computador HP ProDesk", "Computador", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("PC05", "Computador HP ProDesk", "Computador", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("PC06", "Computador HP ProDesk", "Computador", "Avariado", "Laboratório 1"));
        d.add(new Equipamento("PC07", "Computador Lenovo ThinkCentre", "Computador", "Operacional", "Laboratório 2"));
        d.add(new Equipamento("PC08", "Computador Lenovo ThinkCentre", "Computador", "Operacional", "Laboratório 2"));
        d.add(new Equipamento("PC09", "Computador Lenovo ThinkCentre", "Computador", "Operacional", "Laboratório 2"));
        d.add(new Equipamento("PC10", "Computador Lenovo ThinkCentre", "Computador", "Em reparação", "Laboratório 2"));
        d.add(new Equipamento("PC11", "Computador Acer Veriton", "Computador", "Operacional", "Laboratório 2"));
        d.add(new Equipamento("PC12", "Computador Acer Veriton", "Computador", "Operacional", "Laboratório 2"));
        d.add(new Equipamento("PC13", "Computador Acer Veriton", "Computador", "Operacional", "Laboratório 2"));
        d.add(new Equipamento("MON01", "Monitor LED 19 polegadas", "Monitor", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("MON02", "Monitor LED 19 polegadas", "Monitor", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("MON03", "Monitor LED 22 polegadas", "Monitor", "Avariado", "Laboratório 2"));
        d.add(new Equipamento("RTR01", "Router TP-Link Archer", "Router", "Operacional", "Sala de servidores"));
        d.add(new Equipamento("SWT01", "Switch Cisco 24 portas", "Switch", "Operacional", "Sala de servidores"));
        d
                .add(new Equipamento("PRJ01", "Projector Epson EB-X06", "Projector", "Operacional", "Laboratório 1"));
        d.add(new Equipamento("IMP01", "Impressora HP LaserJet", "Impressora", "Em reparação", "Secretaria"));
        return d;
    }

    //Grava todos os equipamentos actuais da tabela num ficheiro CSV na memória rom
    static void opGravarFicheiro() {
        System.out.println("\n--- GRAVAR INVENTÁRIO EM FICHEIRO ---");
        List<Equipamento> lista = tabela.todos();
        if (lista.isEmpty()) {
            System.out.println("  Aviso: o inventário está vazio. Nada foi gravado.");
            return;
        }
        System.out.print("  Nome do ficheiro (Enter para usar '" + FICHEIRO_PADRAO + "'): ");
        String nomeFicheiro = entrada.nextLine().trim();
        if (nomeFicheiro.isEmpty()) nomeFicheiro = FICHEIRO_PADRAO;

        try (BufferedWriter bw = new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(nomeFicheiro), StandardCharsets.UTF_8))) {
            bw.write("Codigo;Designacao;Categoria;Estado;Localizacao");
            bw.newLine();
            for (Equipamento e : lista) {
                bw.write(e.paraLinhaCSV());
                bw.newLine();
            }
            File f = new File(nomeFicheiro);
            System.out.println("  Sucesso: " + lista.size() + " equipamento(s) gravado(s) em:");
            System.out.println("  " + f.getAbsolutePath());
        } catch (IOException ex) {
            System.out.println("  ERRO ao gravar o ficheiro: " + ex.getMessage());
        }
    }
    // Carrega equipamentos de um ficheiro CSV na memória rom para a tabela hash activa.
    static void opCarregarFicheiro() {
        System.out.println("\n--- CARREGAR INVENTÁRIO DE FICHEIRO ---");
        System.out.print("  Nome do ficheiro (Enter para usar '" + FICHEIRO_PADRAO + "'): ");
        String nomeFicheiro = entrada.nextLine().trim();
        if (nomeFicheiro.isEmpty()) nomeFicheiro = FICHEIRO_PADRAO;

        File f = new File(nomeFicheiro);
        if (!f.exists() || !f.isFile()) {
            System.out.println("  ERRO: ficheiro '" + nomeFicheiro + "' não encontrado.");
            return;
        }

        boolean det = tabela.isDetalhado();
        tabela.setDetalhado(false);
        int inseridos = 0, ignorados = 0;

        try (BufferedReader br = new BufferedReader(
                new InputStreamReader(new FileInputStream(f), StandardCharsets.UTF_8))) {
            String linha;
            boolean primeiraLinha = true;
            while ((linha = br.readLine()) != null) {
                linha = linha.trim();
                if (linha.isEmpty()) continue;
                if (primeiraLinha && linha.toLowerCase().startsWith("codigo;")) {
                    primeiraLinha = false;
                    continue;
                }
                primeiraLinha = false;
                Equipamento e = Equipamento.deLinhaCSV(linha);
                if (e != null && tabela.inserir(e)) {
                    inseridos++;
                } else {
                    ignorados++;
                }
            }
            System.out.println("  Leitura concluída: " + inseridos + " equipamento(s) carregado(s), "
                    + ignorados + " ignorado(s)/duplicado(s).");
        } catch (IOException ex) {
            System.out.println("  ERRO ao ler o ficheiro: " + ex.getMessage());
        } finally {
            tabela.setDetalhado(det);
        }
    }

    // 8. INTERFACE COM O UTILIZADOR (menu)
    static Scanner entrada = new Scanner(System.in);
    static TabelaHash tabela;

    static String lerTexto(String mensagem) {
        while (true) {
            System.out.print(mensagem);
            String s = entrada.nextLine().trim();
            if (!s.isEmpty()) return s;
            System.out.println("  Valor inválido: o campo não pode ficar vazio.");
        }
    }

    static int lerInteiro(String mensagem, int min, int max) {
        while (true) {
            System.out.print(mensagem);
            String s = entrada.nextLine().trim();
            try {
                int v = Integer.parseInt(s);
                if (v >= min && v <= max) return v;
            } catch (NumberFormatException ex) {
            }
            System.out.println("  Valor inválido: introduza um número entre " + min + " e " + max + ".");
        }
    }

    static String lerCodigo() {
        while (true) {
            String s = lerTexto("  Código do equipamento (letras, números, '-' ou '_'; ex.: PC01): ");
            if (s.matches("[A-Za-z0-9_\\-]+")) return s.toUpperCase();
            System.out.println("  Código inválido: não use espaços nem símbolos especiais.");
        }
    }

    static String escolherDeLista(String titulo, String[] opcoes) {
        System.out.println("  " + titulo);
        for (int i = 0; i < opcoes.length; i++) {
            System.out.println("    " + (i + 1) + " - " + opcoes[i]);
        }
        int escolha = lerInteiro("  Opção: ", 1, opcoes.length);
        return opcoes[escolha - 1];
    }

    static TabelaHash criarTabela(int metodo, int tamanho) {
        switch (metodo) {
            case 1:  return new TabelaEncadeada(tamanho);
            case 2:  return new TabelaEncadeamentoCoalescido(tamanho);
            case 3:  return new TabelaEnderecamentoAberto(tamanho, TabelaEnderecamentoAberto.Sondagem.LINEAR);
            case 4:  return new TabelaEnderecamentoAberto(tamanho, TabelaEnderecamentoAberto.Sondagem.QUADRATICA);
            default: return new TabelaEnderecamentoAberto(tamanho, TabelaEnderecamentoAberto.Sondagem.DUPLA);
        }
    }
//Menu de escolher o metodo
    static void escolherMetodo(boolean migrar) {
        System.out.println();
        System.out.println("  Métodos de resolução de colisões:");
        System.out.println("    1 - Encadeamento separado (listas externas)");
        System.out.println("    2 - Encadeamento coalescido (listas internas no vector)");
        System.out.println("    3 - Endereçamento aberto: sondagem linear");
        System.out.println("    4 - Endereçamento aberto: sondagem quadrática");
        System.out.println("    5 - Endereçamento aberto: duplo espalhamento");
        int metodo = lerInteiro("  Escolha o método (1-5): ", 1, 5);
        int tamanho = lerInteiro("  Tamanho inicial da tabela (5 a 1000; será ajustado para o primo seguinte; sugestão 11): ",
                5, 1000);

        List<Equipamento> existentes = new ArrayList<Equipamento>();
        boolean det = false;
        if (migrar && tabela != null && tabela.getN() > 0) {
            String r = lerTexto("  Migrar os " + tabela.getN() + " equipamentos actuais para a nova tabela? (S/N): ");
            if (r.equalsIgnoreCase("S")) existentes = tabela.todos();
        }
        if (tabela != null) det = tabela.isDetalhado();
        tabela = criarTabela(metodo, tamanho);
        tabela.setDetalhado(det);
        for (Equipamento e : existentes) tabela.inserir(e);
        System.out.println("  Nova tabela criada: " + tabela.nome() + " (m = " + tabela.getM() + ").");
        if (!existentes.isEmpty()) System.out.println("  Equipamentos migrados: " + existentes.size() + ".");
    }
//Inserir novo Equipamento
    static void opRegistar() {
        System.out.println("\n--- REGISTAR EQUIPAMENTO ---");
        String codigo = lerCodigo();
        String designacao = lerTexto("  Designação (ex.: Computador Dell OptiPlex): ");
        String categoria = escolherDeLista("Categoria:", CATEGORIAS);
        String estado = escolherDeLista("Estado:", ESTADOS);
        String local = lerTexto("  Localização (ex.: Laboratório 1): ");
        Equipamento e = new Equipamento(codigo, designacao, categoria, estado, local);
        if (tabela.inserir(e)) {
            System.out.println("  Equipamento " + codigo + " registado com sucesso.");
        } else {
            System.out.println("  Não foi possível registar: o código " + codigo + " já existe.");
        }
    }
//Pesquisar Equipamentos
    static void opPesquisar() {
        System.out.println("\n--- PESQUISAR EQUIPAMENTO ---");
        String codigo = lerCodigo();
        long antes = tabela.getComparacoes();
        Equipamento e = tabela.pesquisar(codigo);
        long gastas = tabela.getComparacoes() - antes;
        if (e == null) {
            System.out.println("  Equipamento " + codigo + " não encontrado (" + gastas + " comparação(ões)).");
        } else {
            System.out.println("  Encontrado (" + gastas + " comparação(ões)):");
            System.out.println("  " + Equipamento.cabecalho());
            System.out.println("  " + e);
        }
    }
//Eliminar
    static void opRemover() {
        System.out.println("\n--- Eliminar Equimento (REMOVER) ---");
        String codigo = lerCodigo();
        if (tabela.remover(codigo)) {
            System.out.println("  Equipamento " + codigo + " removido do inventário.");
        } else {
            System.out.println("  Equipamento " + codigo + " não existe.");
        }
    }
//Actualização do estado dos Equimentos
    static void opActualizarEstado() {
        System.out.println("\n--- ACTUALIZAR ESTADO ---");
        String codigo = lerCodigo();
        String estado = escolherDeLista("Novo estado:", ESTADOS);
        if (tabela.actualizarEstado(codigo, estado)) {
            System.out.println("  Estado de " + codigo + " actualizado para \"" + estado + "\".");
        } else {
            System.out.println("  Equipamento " + codigo + " não existe.");
        }
    }
//Lista de todos os equipamentos
    static void opListar() {
        System.out.println("\n--- INVENTÁRIO (pela ordem das posições da tabela) ---");
        List<Equipamento> lista = tabela.todos();
        if (lista.isEmpty()) {
            System.out.println("  O inventário está vazio.");
            return;
        }
        System.out.println("  " + Equipamento.cabecalho());
        for (Equipamento e : lista) System.out.println("  " + e);
        System.out.println("  Total: " + lista.size() + " equipamento(s).");
        System.out.println("  Nota: uma tabela hash não mantém ordem alfabética; a ordem depende de h(k).");
    }
//Demonstração de exemplos
    static void opCarregarDemo() {
        boolean det = tabela.isDetalhado();
        tabela.setDetalhado(false);
        int novos = 0, repetidos = 0;
        for (Equipamento e : dadosDemonstracao()) {
            if (tabela.inserir(e)) novos++; else repetidos++;
        }
        tabela.setDetalhado(det);
        System.out.println("\n  Dados de demonstração: " + novos + " inserido(s), " + repetidos + " já existente(s).");
    }
//Responsável por mostrar as comparações dos metodos
    static void opComparar() {
        System.out.println("\n--- COMPARAÇÃO DOS 5 MÉTODOS (mesmos 20 equipamentos, m inicial = "
                + TAMANHO_INICIAL + ") ---");
        String[] nomes = {"Encad. Separado", "Encad. Coalesc.", "Linear", "Quadrática", "Duplo espalh."};
        mostrarAvisoRehash = false;
        System.out.println(String.format("  %-15s | %4s | %3s | %6s | %8s | %7s | %-18s",
                "Método", "m", "n", "Carga", "Colisões", "Rehash", "Comp./pesquisa"));
        System.out.println("  ----------------+------+-----+--------+----------+---------+-------------------");
        for (int metodo = 1; metodo <= 5; metodo++) {
            TabelaHash t = criarTabela(metodo, TAMANHO_INICIAL);
            List<Equipamento> dados = dadosDemonstracao();
            for (Equipamento e : dados) t.inserir(e);
            long colisoesInsercao = t.getColisoes();
            long antes = t.getComparacoes();
            for (Equipamento e : dados) t.pesquisar(e.getCodigo());
            double media = (double) (t.getComparacoes() - antes) / dados.size();
            System.out.println(String.format("  %-15s | %4d | %3d | %6.3f | %8d | %7d | %-18.3f",
                    nomes[metodo - 1], t.getM(), t.getN(), t.factorCarga(), colisoesInsercao,
                    t.getRehashes(), media));
        }
        mostrarAvisoRehash = true;
        System.out.println("  Carga = n/m final. Comp./pesquisa = média de chaves comparadas ao pesquisar cada equipamento.");
    }
//Menu interativo
    static void mostrarMenu() {
        System.out.println();
        System.out.println("==================================================================");
        System.out.println("  GESTÃO DE EQUIPAMENTOS - LABORATÓRIO DE INFORMÁTICA");
        System.out.println("  Método activo: " + tabela.nome());
        System.out.println("  m = " + tabela.getM() + " | n = " + tabela.getN()
                + String.format(" | carga = %.3f", tabela.factorCarga())
                + " | modo passo a passo: " + (tabela.isDetalhado() ? "LIGADO" : "desligado"));
        System.out.println("==================================================================");
        System.out.println("   1 - Registar equipamento (inserir)");
        System.out.println("   2 - Pesquisar equipamento por código");
        System.out.println("   3 - Eliminar (remover)");
        System.out.println("   4 - Actualizar estado");
        System.out.println("   5 - Listar inventário");
        System.out.println("   6 - Mostrar a estrutura interna da tabela");
        System.out.println("   7 - Estatísticas (carga, colisões, comparações)");
        System.out.println("   8 - Carregar dados de demonstração (20 equipamentos)");
        System.out.println("   9 - Mudar de método / reiniciar a tabela");
        System.out.println("  10 - Comparar os 5 métodos");
        System.out.println("  11 - Ligar/desligar o modo passo a passo");
        System.out.println("  12 - Gravar inventário em ficheiro (.csv)");
        System.out.println("  13 - Carregar inventário de ficheiro (.csv)");
        System.out.println("   0 - Sair");
    }
//responável por escolher a opção, mas primeiro escolhe o metodo
    public static void main(String[] args) {
        System.out.println("SISTEMA DE GESTÃO DE EQUIPAMENTOS - TABELA DE ESPALHAMENTO (HASH TABLE)");
        try {
            escolherMetodo(false);
            int opcao;
            do {
                mostrarMenu();
                opcao = lerInteiro("  Escolha uma opção: ", 0, 13);
                switch (opcao) {
                    case 1:  opRegistar(); break;
                    case 2:  opPesquisar(); break;
                    case 3:  opRemover(); break;
                    case 4:  opActualizarEstado(); break;
                    case 5:  opListar(); break;
                    case 6:  System.out.println(); tabela.mostrarEstrutura(); break;
                    case 7:  System.out.println(); tabela.estatisticas(); break;
                    case 8:  opCarregarDemo(); break;
                    case 9:  escolherMetodo(true); break;
                    case 10: opComparar(); break;
                    case 11:
                        tabela.setDetalhado(!tabela.isDetalhado());
                        System.out.println("  Modo passo a passo: " + (tabela.isDetalhado() ? "LIGADO" : "desligado"));
                        break;
                    case 12: opGravarFicheiro(); break;
                    case 13: opCarregarFicheiro(); break;
                    default: break;
                }
            } while (opcao != 0);
            System.out.println("\n  Programa terminado. Até breve!");
        } catch (NoSuchElementException ex) {
            System.out.println("\n  Fim da entrada de dados. Programa terminado.");
        }
    }
}