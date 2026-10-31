[app]
title = Football Predictor
package.name = footballpredictor
package.domain = org.fp
source.dir = .
source.include_exts = py,json
version = 5.6
requirements = python3,kivy==2.3.0,requests,urllib3,chardet,idna,certifi,charset-normalizer,arabic-reshaper==3.0.0,python-bidi==0.4.2
orientation = portrait
fullscreen = 0
android.permissions = INTERNET,READ_EXTERNAL_STORAGE,WRITE_EXTERNAL_STORAGE
android.api = 33
android.minapi = 24
android.archs = arm64-v8a
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 1
