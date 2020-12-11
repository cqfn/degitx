// MIT License. Copyright (c) 2020 CQFN
// https://github.com/cqfn/degitx/blob/master/LICENSE

package logging

import (
	"errors"
	"sync"

	"cqfn.org/degitx/locators"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

var errLogAlreadyInitialized = errors.New("log already initialized") //nolint:misspell // initialized

type logContext struct {
	internalLogLevel map[string]zapcore.Level
	nodeID           string
	cfg              *LogConfig
	plain            *zapcore.Encoder
	json             *zapcore.Encoder
	registeredLevel  []zap.AtomicLevel
}

var logCtx *logContext //nolint:gochecknoglobals

var mux sync.Mutex //nolint:gochecknoglobals

// Init inits zap logger context from config and predeclared settings.
// Init also adds node ID to logger context.
func Init(node *locators.Node, cfg *LogConfig) {
	InitNodeless(cfg)
	logCtx.nodeID = node.ID.HexString()
}

// InitNodeless inits zap logger context from config and predeclared settings.
func InitNodeless(cfg *LogConfig) {
	mux.Lock()
	defer mux.Unlock()
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
	registeredLevel := []zap.AtomicLevel{}
	for _, out := range cfg.Outputs {
		atomicLevel := zap.NewAtomicLevelAt(internalLogLevel[out.Level])
		registeredLevel = append(registeredLevel, atomicLevel)
	}

	logCtx = &logContext{
		internalLogLevel: internalLogLevel,
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
