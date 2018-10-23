#------------------------------------------------------------------------------#
# This file contains the setup for building a base image for the MiniZinc
# challenges. It uses multi-stage builds in order to keep the images small.
# Note that the statements ADD, RUN, and COPY can add image layers.
#------------------------------------------------------------------------------#
# The build image

FROM minizinc/mznc2018:1.0

# Install Java.
RUN \
  echo oracle-java8-installer shared/accepted-oracle-license-v1-1 select true | debconf-set-selections && \
  apt-get update && \
  apt-get -y install software-properties-common python-software-properties && \
  add-apt-repository -y ppa:webupd8team/java && \
  apt-get update && \
  apt-get install -y oracle-java8-installer && \
  rm -rf /var/lib/apt/lists/* && \
rm -rf /var/cache/oracle-jdk8-installer

ENV JAVA_HOME /usr/lib/jvm/java-8-oracle

# Install Maven

ARG MAVEN_VERSION=3.5.4
ARG USER_HOME_DIR="/root"
ARG SHA=ce50b1c91364cb77efe3776f756a6d92b76d9038b0a0782f7d53acf1e997a14d
ARG BASE_URL=https://apache.osuosl.org/maven/maven-3/${MAVEN_VERSION}/binaries

RUN mkdir -p /usr/share/maven /usr/share/maven/ref \
  && apt-get update \
  && apt-get -y install curl \
  && curl -fsSL -o /tmp/apache-maven.tar.gz ${BASE_URL}/apache-maven-${MAVEN_VERSION}-bin.tar.gz \
  && echo "${SHA}  /tmp/apache-maven.tar.gz" | sha256sum -c - \
  && tar -xzf /tmp/apache-maven.tar.gz -C /usr/share/maven --strip-components=1 \
  && rm -f /tmp/apache-maven.tar.gz \
  && ln -s /usr/share/maven/bin/mvn /usr/bin/mvn

ENV MAVEN_HOME /usr/share/maven
ENV MAVEN_CONFIG "$USER_HOME_DIR/.m2"

# Retrieval of JaCoP

RUN apt-get update \
&& apt-get install -y git \
&& git clone https://github.com/radsz/jacop /jacop

RUN cd /jacop && \
git fetch && \
git checkout 04b17f002bce && \
mvn clean install -DskipTests && \
cp -r /jacop/src/main/minizinc/org/jacop/minizinc/* /entry_data/mzn-lib/


RUN \
    echo "#!/bin/bash                                 " >  /entry_data/fzn-exec && \
    echo "#------------------------------------------#" >> /entry_data/fzn-exec && \
    echo "exec java -server -cp /jacop/target/jacop-*-SNAPSHOT.jar -Xmx10G -Xms10M org.jacop.fz.Fz2jacop \"\$@\" " >> /entry_data/fzn-exec && \
    chmod a+x /entry_data/fzn-exec


