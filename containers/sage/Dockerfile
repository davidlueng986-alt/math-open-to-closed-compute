FROM sagemath/sagemath:10.6
USER root
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends ca-certificates git sudo python3 python3-pip build-essential libgmp-dev nauty z3 minisat && rm -rf /var/lib/apt/lists/*
RUN sage -c 'assert factor(360).value() == 360 and len(factor(360)) == 3' && command -v z3 && command -v minisat && command -v nauty-geng
ENTRYPOINT []
