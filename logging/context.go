// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package logging

import (
	"errors"

	"cqfn.org/degitx/locators"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

type LogConfig struct {
	Outputs   []Output `yaml:"outputs"`
	ErrorsOut []string `yaml:"errors"`
}

type Output struct {
	UniqName string   `yaml:"u_name"`
	Path     []string `yaml:"path"`
	Level    string   `yaml:"level"`
	Format   string   `yaml:"format"`
}

var errLogAlreadyInitialized = errors.New("log already initialized") //nolint:misspell // initialized

type logContext struct {
	internalLogLevel map[string]zapcore.Level
	nodeID           string
	cfg              *LogConfig
	plain            *zapcore.Encoder
	json             *zapcore.Encoder
	registeredLevel  map[string]zap.AtomicLevel
}

var logCtx *logContext //nolint:gochecknoglobals

func Init(node *locators.Node, cfg *LogConfig) {
	node.Mux.Lock()
	defer node.Mux.Unlock()
	if logCtx != nil {
		panic(errLogAlreadyInitialized)
	}
	plainEncoder, jsonEncoder := encoders()

	internalLogLevel := map[string]zapcore.Level{
		"Debug": zapcore.DebugLevel,
		"Info":  zapcore.InfoLevel,
		"Warn":  zapcore.WarnLevel,
		"Error": zapcore.ErrorLevel,
	}
	registeredLevel := map[string]zap.AtomicLevel{}
	for _, out := range cfg.Outputs {
		_, ok := registeredLevel[out.UniqName]
		if !ok {
			atomicLevel := zap.NewAtomicLevelAt(internalLogLevel[out.Level])
			registeredLevel[out.UniqName] = atomicLevel
		}
	}

	logCtx = &logContext{
		internalLogLevel: internalLogLevel,
		nodeID:           node.ID.HexString(),
		cfg:              cfg,
		plain:            plainEncoder,
		json:             jsonEncoder,
		registeredLevel:  registeredLevel,
	}
}

func encoders() (*zapcore.Encoder, *zapcore.Encoder) {
	consoleEncoderConfig := zapcore.EncoderConfig{
		TimeKey:        "Time",
		LevelKey:       "Level",
		NameKey:        zapcore.OmitKey,
		CallerKey:      zapcore.OmitKey,
		FunctionKey:    zapcore.OmitKey,
		MessageKey:     "Message",
		StacktraceKey:  zapcore.OmitKey,
		LineEnding:     zapcore.DefaultLineEnding,
		EncodeLevel:    zapcore.CapitalColorLevelEncoder,
		EncodeTime:     zapcore.ISO8601TimeEncoder,
		EncodeDuration: zapcore.StringDurationEncoder,
		EncodeCaller:   zapcore.ShortCallerEncoder,
	}
	plainEncoder := zapcore.NewConsoleEncoder(consoleEncoderConfig)
	jsonEncoderConfig := consoleEncoderConfig
	jsonEncoderConfig.EncodeLevel = zapcore.CapitalLevelEncoder
	jsonEncoder := zapcore.NewJSONEncoder(jsonEncoderConfig)
	return &plainEncoder, &jsonEncoder
}

func openSinks(paths []string) (zapcore.WriteSyncer, func(), error) {
	sink, closeOut, err := zap.Open(paths...)
	if err != nil {
		return nil, nil, err
	}
	return sink, closeOut, nil
}

func openErrorSinks(paths []string, closeOuts []func()) (zapcore.WriteSyncer, error) {
	errSink, _, err := zap.Open(paths...)
	if err != nil {
		for _, closeOut := range closeOuts {
			closeOut()
		}
		return nil, err
	}
	return errSink, nil
}
