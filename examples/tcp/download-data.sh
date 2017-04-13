#!/bin/bash

if [ ! -d ./20_newsgroups ]; then
	wget http://qwone.com/~jason/20Newsgroups/20news-19997.tar.gz -O 20news-19997.tar.gz
    tar -xzvf 20news-19997.tar.gz
fi


