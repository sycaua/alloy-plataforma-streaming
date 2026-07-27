/*
 * Assinaturas base
 */

abstract sig TipoDeConteudo {}
one sig Filme, Serie, Documentario extends TipoDeConteudo {}

abstract sig ClassificacaoIndicativa {}
one sig Livre, ApenasAdolescentes, ApenasAdultos extends ClassificacaoIndicativa {}

// Básico < Plus < Premium
abstract sig Plano {}
one sig Basico, Plus, Premium extends Plano {}

sig Conteudo {
    tipoDoConteudo: one TipoDeConteudo,
    classificacaoIndicativa: one ClassificacaoIndicativa,

    /*
     * Conteúdos podem ser exigir um tipo de plano mínimo para permitir o acesso.
     *
     * Básico = Sem exigências
     * Plus = Exige plano Plus ou Premium
     * Premium  = Exige plano Premium
     */
    planoMinimo: one Plano
}

sig Usuario {
    planoAssinado: one Plano,
    perfisAssociados: set Perfil,
    perfisEmUso: set Perfil
}

sig Perfil {
    contaAssociada: one Usuario,
    catalogoAcessivel: set Conteudo,
    estahAssistindo: set Conteudo
}

/*
 * Fatos e regras
 */

// Fato: plataforma não pode ser vazia.
fact PlataformaNaoVazia {
    some Conteudo
}

// Fato: todo perfil é associado a exatamente um usuário.
fact AssociacaoPerfil {
    all u : Usuario | u.perfisAssociados = u.~contaAssociada
}

// Fato: perfis em uso pertencem ao mesmo usuário.
fact AssociacaoPerfilEmUso {
    all u : Usuario | u.perfisEmUso in u.perfisAssociados
}

// Fato: apenas perfis ativos (isto é, que estão assistindo algo) acessam conteúdos.
fact AcesssoAtivo {
    all u : Usuario | all pf : u.perfisAssociados | pf in u.perfisEmUso iff some pf.estahAssistindo
}

// Fato: perfis só podem assistir conteúdos acessíveis.
fact ApenasAcessosPossiveis {
    all pf : Perfil | pf.estahAssistindo in pf.catalogoAcessivel
}

// Fato: restrições numéricas do número de perfis acessando conteúdos por tipo de plano assinado.
fact LimitacoesNumericasPlanos {

    // Plano Básico: no máximo dois perfis simultâneos.
    all u : Usuario | u.planoAssinado = Basico implies #u.perfisEmUso <= 2

    // Plano Plus: no máximo quatro perfis simultâneos.
    all u : Usuario | u.planoAssinado = Basico implies #u.perfisEmUso <= 4

    // Plano Premium: sem limites de perfis.
}

// Fato: o acesso aos conteúdos é definido pelo tipo de plano do usuário.
fact LimitacoesDeAcessoPlanos {

    // Plano Básico só libera acesso aos conteúdos básicos.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Basico implies 
        all c : pf.catalogoAcessivel | c.planoMinimo = Basico

    // Plano Plus libera acesso aos conteúdos básicos e aos pluses, mas não aos premiums.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Plus implies
            all c : pf.catalogoAcessivel | c.planoMinimo != Premium
}

/*
 * Asserts e testes
 */

// Plataforma vazia
assert PlataformaVazia {
    some Conteudo
} 

// Toda perfil deve ter um usuario
assert PerfilPertenceAoUsuario {
    all p : Perfil | p in p.contaAssociada.perfisAssociados
}

// Usuarios com contas basicas so podem ter no maximo 2 perfis
assert TamanhoMaximoBasico {
    no u : Usuario | u.planoAssinado = Basico and #u.perfisAssociados > 2
}

// Usuarios com contas premium so podem ter no maximo 4 perfis
assert TamanhoMaximoPlus {
    no u : Usuario | u.planoAssinado = Plus and #u.perfisAssociados > 4
}

// usuarios de plano basico so podem acessar conteudo basico
assert BasicoAcessaApenasBasico {
    no pf : Perfil | pf.contaAssociada.planoAssinado = Basico and
        some c : pf.catalogoAcessivel | c.planoMinimo != Basico
}

// usuarios do plano basico não podem acessar conteudos plus ou premium
assert BasicoNaoAcessaPlusNemPremium {
    all p : Perfil | p.contaAssociada.planoAssinado = Basico implies
        all c : p.catalogoAcessivel | c.planoMinimo = Basico
}

// usuarios do plano plus não podem acessar conteudos premium
assert PlusNaoAcessaPremium {
    all p : Perfil | p.contaAssociada.planoAssinado = Plus implies
        all c : p.catalogoAcessivel | c.planoMinimo != Premium 
}

// usuarios do plano plus podem acessar conteudos basicos
assert PlusAcessaTodoBasico {
    all p : Perfil | p.contaAssociada.planoAssinado = Plus implies
        all c : Conteudo | c.planoMinimo = Basico implies
            c in p.catalogoAcessivel
}

// usuarios premium podem acessar todos os conteudos
assert PremiumTemAcessoATudo {
    all p : Perfil | p.contaAssociada.planoAssinado = Premium implies
        all c : Conteudo | c in p.catalogoAcessivel
}

check PlataformaVazia for 5
check PerfilPertenceAoUsuario for 5
check TamanhoMaximoBasico for 5
check TamanhoMaximoPlus for 5
check BasicoAcessaApenasBasico for 5
check BasicoNaoAcessaPlusNemPremium for 5
check PlusNaoAcessaPremium for 5
check PlusAcessaTodoBasico for 5
check PremiumTemAcessoATudo for 5

run {} for 5
