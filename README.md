# Modelagem em Alloy de Sistema de Plataforma de Streaming

Código desenvolvido como projeto da disciplina de Lógica para Computação (período 2026.1) no curso de Bacharelado em Ciência da Computação da Universidade Federal de Campina Grande (UFCG).

O sistema têm as seguintes características:
- A plataforma é composta por conteúdos, usuários e perfis.
- A plataforma deve conter, no mínimo, um conteúdo, um usuário e um perfil.
- Os conteúdos podem ser séries, filmes ou documentários.
- Todo conteúdo pode ter classificação indicativa, restrita às opções "livre para todas as idades", "apenas para adolescentes" ou "apenas para adultos".
- Um único usuário pode ter multiplos perfis, cada um independente do outro.
- Os conteúdos são acessados por meio de um perfil.
- A classificação indicativa tem caráter informativo e não impede a reprodução do conteúdo pelo perfil.
- Um usuário tem três opções de plano para assinar: Básico, Plus ou Premium.
- Usuários com o Plano Básico podem ter, no máximo, dois perfis acessando conteúdo simultâneamente.
- Usuários com o Plano Plus podem ter, no máximo, quatro perfis acessando conteúdo simultâneamente.
- Usuários com o Plano Premium não têm restrições de acesso quanto aos perfis.
- Conteúdos podem exigir um tipo mínimo de plano para serem reproduzidos, onde o Básico é o padrão.
- Um usuário de Plano Básico só pode reproduzir, nos seus perfis, conteúdos com nível básico.
- Um usuário de Plano Plus pode reproduzir, nos seus perfis, conteúdos com nível básico ou plus.
- Um usuário de Plano Premium não possui restrições de nível de plano.
