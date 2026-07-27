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
    perfisAssociados: set Perfil 
}

sig Perfil {
    contaAssociada: one Usuario,
    catalogoAcessivel: set Conteudo
}

// Fato: uma única plataforma para todos os componentes.
fact PlataformaUnica {
    all c : Conteudo | one p : Plataforma | c in p.conteudos

    all u : Usuario |
        one p : Plataforma | u in p.usuarios

    all pf : Perfil |
        one p : Plataforma | pf in p.perfis
}

// Fato: todo perfil é associado a exatamente um usuário.
fact AssociacaoPerfil {
    all u : Usuario | u.perfisAssociados = u.~contaAssociada
}

// Fato: restrições numéricas dos números de perfis permitidos por tipo de plano assinado.
fact LimitacoesNumericasPlanos {

    // Plano Básico: no máximo dois perfis simultâneos.
    all u : Usuario |
        u.planoAssinado = Basico implies #u.perfisAssociados <= 2

    // Plano Plus: no máximo quatro perfis simultâneos.
    all u : Usuario | u.planoAssinado = Plus implies #u.perfisAssociados <= 4

    // Plano Premium: sem limites de perfis.
    all u : Usuario | u.planoAssinado = Premium implies #u.perfisAssociados >= 0
}

// Fato: o acesso aos conteúdos é definido pelo tipo de plano do usuário.
fact LimitacoesDeAcessoPlanos {

    // Plano Básico só libera acesso aos conteúdos básicos.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Basico implies 
        all c : pf.catalogoAcessivel | c.planoMinimo = Basico

    // Plano Plus libera acesso aos conteúdos básicos e aos pluses, mas não aos premiums.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Plus implies
            all c : pf.catalogoAcessivel | c.planoMinimo != Premium

    // Plano Premium libera acesso a todos os conteúdos.
    all pf : Perfil | pf.contaAssociada.planoAssinado = Premium implies
            all c : pf.catalogoAcessivel | c.planoMinimo in Plano
}

// Testes:

// Plataforma vazia
assert PlataformaVazia {
    no p : Plataforma | #p.conteudos = 0 and #p.usuarios = 0 and #p.perfis = 0
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
